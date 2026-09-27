#!/usr/bin/env python3
"""Explicit pinned dependency setup; never invoked by check.py. Apache-2.0."""
import argparse
from datetime import datetime, timezone
import os
from pathlib import Path, PurePosixPath
import posixpath
import re
import shutil
import subprocess
import sys
import tarfile
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import (ROOT, LEAN, require, digest, source_lock, source_manifest, imports,
                    check_dependencies, compiler_bin, fresh_run, write_json, lean_env, NAME)

def dependency_header(text):
    """Read imports and the split-module marker from a comment-stripped header."""
    result, clean, depth, quoted, escaped = [], [], 0, False, False
    split_module = False
    i = 0
    while i < len(text):
        char = text[i]
        if not quoted and text.startswith('/-', i):
            depth += 1
            i += 2
            continue
        if depth and text.startswith('-/', i):
            depth -= 1
            i += 2
            continue
        if not depth and not quoted and text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
            continue
        if not depth:
            clean.append(char)
            if quoted:
                if escaped:
                    escaped = False
                elif char == '\\':
                    escaped = True
                elif char == '"':
                    quoted = False
            elif char == '"':
                quoted = True
        i += 1
        if char != '\n' and i != len(text):
            continue
        line = ''.join(clean).strip()
        clean = []
        if not line or line == 'prelude':
            continue
        if line == 'module':
            split_module = True
            continue
        match = re.fullmatch(r'(?:(?:public|meta)\s+)*import\s+(?:all\s+)?(.+)', line)
        if not match:
            require(line != 'import', 'Unsupported multiline dependency import')
            return result, split_module
        names = match[1].split()
        require(all(NAME.fullmatch(name) for name in names), 'Unsupported dependency module name')
        result.extend(names)
    require(depth == 0, 'Unclosed dependency header comment')
    return result, split_module

def dependency_imports(text):
    """Read dependency imports, not comments or tactic bodies."""
    return dependency_header(text)[0]

def inspect_archive(bundle):
    members = bundle.getmembers()
    by_name = {m.name.rstrip('/'): m for m in members}
    roots = set()
    require(len(by_name) == len(members), 'Duplicate archive names')
    for m in members:
        path = PurePosixPath(m.name)
        require(path.parts and not path.is_absolute() and '..' not in path.parts
                and '.git' not in path.parts, 'Unsafe archive path')
        roots.add(path.parts[0])
        safe_link = m.issym() and not PurePosixPath(m.linkname).is_absolute()
        if safe_link:
            target = posixpath.normpath(str(path.parent / m.linkname))
            safe_link = target.startswith(path.parts[0] + '/') and target in by_name and by_name[target].isfile()
        require(m.isfile() or m.isdir() or safe_link, 'Unsupported archive member')
        for parent in path.parents:
            require(str(parent) not in by_name or by_name[str(parent)].isdir(), 'Non-directory archive parent')
    require(len(roots) == 1 and sum(m.size for m in members) < 1024**3, 'Unexpected source archive shape/size')
    return roots.pop()

def fetch(archive_directory=None):
    packages = LEAN / '.lake/packages'
    packages.mkdir(parents=True, exist_ok=True)
    run = fresh_run('dependency-sources')
    lock = source_lock()
    for item in lock['packages']:
        destination = packages / item['name']
        if destination.exists():
            print('Retaining existing source tree: ' + item['name'], flush=True)
            continue
        archive = run / (item['name'] + '.tar.gz')
        if archive_directory:
            shutil.copyfile(archive_directory / archive.name, archive)
        else:
            expected = item['repository'].replace('https://github.com/', 'https://codeload.github.com/')
            require(item['archive_url'] == expected + '/tar.gz/' + item['commit'], 'Unexpected source URL')
            subprocess.run(['curl', '--disable', '--fail', '--silent', '--show-error', '--proto', '=https',
                            '--connect-timeout', '20', '--max-time', '240', '--max-filesize', '104857600',
                            '--output', str(archive), item['archive_url']], check=True)
        require(digest(archive) == item['archive_sha256'], 'Archive checksum differs: ' + item['name'])
        extraction = run / ('extract-' + item['name'])
        extraction.mkdir()
        with tarfile.open(archive, 'r:gz') as bundle:
            prefix = inspect_archive(bundle)
            bundle.extractall(extraction, filter='data')
        shutil.move(str(extraction / prefix), destination)
        print('Installed pinned source: ' + item['name'], flush=True)
    receipt = check_dependencies(packages)
    write_json(run / 'receipt.json', {'scope': 'Dependency sources only; not proof verification', 'packages': receipt})
    print('PASS pinned sources; build caches are a separate setup step.')

def cache(supplied_bin=None):
    """Use Mathlib's official cache utility with the preserved path-dependency layout."""
    packages = LEAN / '.lake/packages'
    check_dependencies(packages)
    bindir = compiler_bin(supplied_bin)
    run = fresh_run('dependency-cache')
    env = os.environ.copy()
    for key in ['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'MATHLIB_CACHE_GET_URL', 'MATHLIB_CACHE_REPO_SCOPE']:
        env.pop(key, None)
    env.update(PATH=str(bindir) + os.pathsep + env.get('PATH', ''), LAKE_NO_CACHE='1',
               MATHLIB_NO_CACHE_ON_UPDATE='1', MATHLIB_CACHE_BASE_URL='https://cache.mathlib.org')
    for key, folder in [('MATHLIB_CACHE_DIR', 'mathlib'), ('LAKE_CACHE_DIR', 'lake'),
                        ('CURL_HOME', 'curl-empty'), ('TMPDIR', 'tmp')]:
        path = LEAN / '.lake/cache' / folder
        path.mkdir(parents=True, exist_ok=True)
        env[key] = str(path)
    env['TMP'] = env['TEMP'] = env['TMPDIR']
    selected = sorted({m for p in source_manifest()['sha256'] for m in imports(ROOT / p)
                       if m.startswith('Mathlib.')})
    require(selected, 'No explicit Mathlib import selection')
    commands = []
    def command(args, cwd=LEAN):
        args = list(map(str, args))
        commands.append(args)
        logfile = run / f'{len(commands):02d}.log'
        print('Dependency setup; log: ' + str(logfile), flush=True)
        with logfile.open('w') as log:
            result = subprocess.run(args, cwd=cwd, env=env, stdout=log, stderr=subprocess.STDOUT)
        require(result.returncode == 0, 'Dependency setup failed; inspect ' + str(logfile))
    command([bindir / 'lake', '--no-cache', 'build', 'cache'])
    mathlib = packages / 'mathlib'
    env['LEAN_SRC_PATH'] = os.pathsep.join(str(packages / p['name']) for p in source_lock()['packages'])
    command([mathlib / '.lake/build/bin/cache', 'get-', '--repo=leanprover-community/mathlib4',
             '--cache-from=master', *selected], cwd=mathlib)
    env.pop('LEAN_SRC_PATH')
    command([bindir / 'lake', '--no-cache', 'exe', 'cache', 'unpack'])
    checks = check_dependencies(packages)
    write_json(run / 'receipt.json', {'scope': 'Official dependency cache acquisition, not proof verification',
                                     'cache_origin': 'https://cache.mathlib.org', 'commands': commands,
                                     'requested_imports': selected, 'source_checks': checks})
    print('Cache commands completed. check.py verify is the full local-source check.', flush=True)

def missing_artifacts(olean, split_module):
    """Artifact presence required by this pinned direct-compiler workflow.

    Lean 4.34 readModuleDataPartsOfMod loads both split olean sidecars;
    readIRPartsOfMod loads .ir when .ir.sig exists. writeModule emits both
    IR parts for our non-postponed direct builds. Require that complete pair
    for split caches too, rather than silently accepting absent IR metadata.
    This checks completeness, not artifact authenticity or proof acceptance.
    """
    olean = Path(olean)
    required = [olean]
    if split_module:
        required += [Path(str(olean) + '.server'), Path(str(olean) + '.private'),
                     olean.with_suffix('.ir.sig'), olean.with_suffix('.ir')]
    elif olean.with_suffix('.ir.sig').exists():
        required.append(olean.with_suffix('.ir'))
    return [path for path in required if not path.is_file()]

def recover(modules=None, packages=None, supplied_bin=None):
    """Offline source compilation of missing imported Lean artifacts; no Lake hooks."""
    packages = Path(packages or LEAN / '.lake/packages').expanduser().resolve()
    before = check_dependencies(packages)
    manifest = source_manifest()
    bindir = compiler_bin(supplied_bin)
    compiler_hash = digest(bindir / 'lean')
    selected = modules or sorted({m for p in manifest['sha256'] for m in imports(ROOT / p)
                                  if not m.startswith(('ReyZygmund.', 'Verification.', 'Lean'))})
    require(selected and all(NAME.fullmatch(m) for m in selected), 'Expected explicit Lean module names')
    run = fresh_run('dependency-recovery')
    stage = run / 'objects'
    stage.mkdir()
    lookup = run / 'lookup'
    lookup.mkdir()
    # Lean resolves a package namespace at the first matching search root.
    # Do not put the partial staging tree before the complete package cache.
    # Each recovered module is installed before its dependents are compiled.
    env = lean_env(bindir, packages, lookup, run)
    record = dict(status='RUNNING', scope='Offline pinned dependency artifact recovery, not project proof acceptance',
                  started_utc=datetime.now(timezone.utc).isoformat(), requested=selected,
                  dependency_sources=before, compiler_sha256=compiler_hash,
                  source_lock_sha256=digest(LEAN / 'SOURCE_LOCK.json'),
                  network_operations=False, lake_build_hooks=False, built=[], reused=[], commands=[])
    def save():
        write_json(run / 'receipt.json', record)
    done, active = set(), set()
    owners = [packages / p['name'] for p in source_lock()['packages']]
    def visit(module):
        if module in done:
            return
        require(module not in active, 'Cyclic dependency imports: ' + module)
        require(NAME.fullmatch(module), 'Unsupported dependency import: ' + module)
        relative = Path(module.replace('.', '/'))
        matches = [owner for owner in owners if (owner / relative.with_suffix('.lean')).is_file()]
        require(len(matches) <= 1, 'Ambiguous dependency module: ' + module)
        if not matches:
            require((bindir.parent / 'lib/lean' / relative.with_suffix('.olean')).is_file(),
                    'No pinned source or toolchain object for: ' + module)
            done.add(module)
            return
        owner = matches[0]
        source = owner / relative.with_suffix('.lean')
        active.add(module)
        for dependency in dependency_imports(source.read_text()):
            visit(dependency)
        destination = owner / '.lake/build/lib/lean' / relative.with_suffix('.olean')
        _, modern = dependency_header(source.read_text())
        absent = missing_artifacts(destination, modern)
        if not absent:
            record['reused'].append(module)
        else:
            require(destination.parent.resolve().is_relative_to(packages), 'Cache directory escapes package root')
            output = stage / relative.with_suffix('.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            options = ['-DautoImplicit=false', '-DmaxSynthPendingDepth=3'] if owner.name == 'mathlib' else []
            command = [str(bindir / 'lean'), *options, '-o', str(output),
                       '-i', str(stage / relative.with_suffix('.ilean')), str(relative.with_suffix('.lean'))]
            log = run / f'build-{len(record["commands"]):03d}.log'
            started = time.monotonic()
            with log.open('w') as stream:
                result = subprocess.run(command, cwd=owner, env=env, stdout=stream,
                                        stderr=subprocess.STDOUT, timeout=1800)
            record['commands'].append(dict(module=module, args=command, exit_code=result.returncode,
                                           seconds=round(time.monotonic()-started, 3),
                                           log=log.name, log_sha256=digest(log)))
            save()
            require(result.returncode == 0 and output.is_file(),
                    'Dependency source build failed; inspect ' + str(log))
            generated = sorted(p for p in output.parent.glob(relative.name + '.*') if p.is_file())
            require(not missing_artifacts(output, modern), 'Compiler omitted required artifact family')
            destination.parent.mkdir(parents=True, exist_ok=True)
            require(all(not (destination.parent / artifact.name).is_symlink() for artifact in generated),
                    'Refusing to replace a symlinked cache artifact')
            artifacts = {}
            for artifact in generated:
                target = destination.parent / artifact.name
                require(not target.is_symlink(), 'Refusing to replace a symlinked cache artifact')
                if target.exists():
                    backup = run / 'previous' / relative.parent / target.name
                    backup.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(target, backup)
                # A successful build installs only this module's generated artifacts.
                shutil.copyfile(artifact, target)
                artifacts[str(target.relative_to(packages))] = digest(target)
            require(not missing_artifacts(destination, modern), 'Installed artifact family is incomplete')
            record['built'].append(dict(module=module, artifacts=artifacts,
                                        missing_before=[str(path.relative_to(packages)) for path in absent]))
            print('Recovered from pinned source: ' + module, flush=True)
            save()
        active.remove(module)
        done.add(module)
    save()
    try:
        for module in selected:
            require(any((owner / Path(module.replace('.', '/')).with_suffix('.lean')).is_file() for owner in owners),
                    'Requested recovery module is not in the pinned dependency sources: ' + module)
            visit(module)
        require(check_dependencies(packages) == before, 'Dependency sources changed during recovery')
        require(source_manifest() == manifest, 'Project sources changed during recovery')
        require(digest(bindir / 'lean') == compiler_hash, 'Compiler changed during recovery')
        record['status'] = 'PASS_DEPENDENCY_RECOVERY'
    except BaseException as failure:
        record['status'] = 'FAIL'
        record['failure'] = str(failure)
        raise
    finally:
        record['finished_utc'] = datetime.now(timezone.utc).isoformat()
        save()
    print('Receipt: ' + str(run / 'receipt.json'), flush=True)
    return run / 'receipt.json'

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['fetch', 'cache', 'recover', 'check'])
    parser.add_argument('--archives', type=Path, help='Offline archive directory, with NAME.tar.gz files')
    parser.add_argument('--lean-bin')
    parser.add_argument('--packages', type=Path, help='For recover/check: explicit pinned package directory; recover writes compiled artifacts here')
    parser.add_argument('--module', action='append', help='For recover: an explicit missing dependency module; repeat as needed')
    args = parser.parse_args()
    if args.mode == 'fetch':
        require(args.packages is None and args.module is None, '--packages/--module do not apply to fetch')
        fetch(args.archives)
    elif args.mode == 'cache':
        require(args.archives is None and args.packages is None and args.module is None, 'Unsupported cache option')
        cache(args.lean_bin)
    elif args.mode == 'recover':
        require(args.archives is None, '--archives applies only to fetch')
        recover(args.module, args.packages, args.lean_bin)
    else:
        require(args.archives is None and args.module is None, 'Unsupported check option')
        check_dependencies(args.packages or LEAN / '.lake/packages')
        print('PASS pinned dependency sources')
