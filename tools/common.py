"""Shared public checking utilities. SPDX-License-Identifier: Apache-2.0"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean'
ALLOW = {'propext', 'Classical.choice', 'Quot.sound'}
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")

def require(condition, message):
    if not condition:
        raise ValueError(message)

def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

def read_json(path):
    return json.loads(Path(path).read_text())

def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')

def source_lock():
    return read_json(LEAN / 'SOURCE_LOCK.json')

def source_manifest():
    manifest = read_json(ROOT / 'verification/SOURCE-MANIFEST.json')
    require(manifest['local_module_count'] == 363, 'Unexpected local module count')
    require(manifest['registered_declaration_count'] == 453, 'Unexpected target count')
    files = manifest['sha256']
    actual = {str(p.relative_to(ROOT)) for base in ['ReyZygmund', 'Verification']
              for p in (LEAN / base).rglob('*.lean')}
    require(len(files) == 363 and actual == set(files), 'Local source inventory differs')
    for name, expected in files.items():
        path = ROOT / name
        require(not path.is_symlink() and path.is_file() and digest(path) == expected,
                'Reviewed source bytes differ: ' + name)
    return manifest

def targets():
    result = read_json(ROOT / 'verification/TARGETS.json')['declarations']
    require(len(result) == 453 and len({d['name'] for d in result}) == 453,
            'Expected 453 distinct declarations')
    for d in result:
        require(set(d) == {'name', 'module', 'contract', 'contract_module'}, 'Target schema differs')
        require(all(NAME.fullmatch(s) for s in d.values()), 'Invalid declaration/module name')
    binding = read_json(ROOT / 'verification/AUDIT-MANIFEST.json')['sha256']
    require(digest(ROOT / 'verification/TARGETS.json') == binding['verification/TARGETS.json'],
            'Reviewed declaration/contract mapping differs')
    return result

def check_dependencies(packages):
    """Check the archive-backed source trees, not independent proof replay of Mathlib."""
    packages = Path(packages).resolve()
    lock = source_lock()
    manifest = read_json(LEAN / 'lake-manifest.json')
    entries = {p['name']: p for p in manifest['packages']}
    require(set(entries) == {p['name'] for p in lock['packages']}, 'Dependency names differ')
    require((LEAN / 'lean-toolchain').read_text().strip() == lock['toolchain'], 'Toolchain differs')
    result = []
    for item in lock['packages']:
        name = item['name']
        entry = entries[name]
        require(entry['type'] == 'path' and entry['dir'] == item['local_path'], 'Manifest differs: ' + name)
        directory = packages / name
        require(directory.is_dir(), 'Missing dependency: ' + name + '; run tools/dependencies.py fetch')
        rows = []
        for current, dirs, files in os.walk(directory, followlinks=False):
            require('.git' not in dirs + files, 'Expected archive-backed dependency, not a Git checkout')
            dirs[:] = [d for d in dirs if d != '.lake']
            require(not any((Path(current) / d).is_symlink() for d in dirs), 'Directory symlink in dependency')
            for filename in files:
                path = Path(current) / filename
                relative = path.relative_to(directory).as_posix()
                if name == 'proofwidgets' and relative == 'widget/package-lock.json.hash':
                    continue
                content = 'symlink:' + str(path.readlink()) if path.is_symlink() else digest(path)
                rows.append((relative, f'{relative}\0{content}\n'))
        rows.sort(key=lambda item: Path(item[0]))
        actual = hashlib.sha256(''.join(row for _, row in rows).encode()).hexdigest()
        require(len(rows) == item['source_file_count'] and actual == item['source_tree_sha256'],
                'Dependency source identity differs: ' + name)
        result.append({'name': name, 'commit': item['commit'], 'source_tree_sha256': actual})
    return result

def compiler_bin(supplied=None):
    if supplied:
        directory = Path(supplied).expanduser().resolve()
    else:
        elan = shutil.which('elan')
        require(elan, 'Install the pinned Lean toolchain with elan, or supply --lean-bin')
        result = subprocess.run([elan, 'which', 'lean'], cwd=LEAN, check=True,
                                capture_output=True, text=True)
        directory = Path(result.stdout.strip()).resolve().parent
    tool = directory / 'lean'
    result = subprocess.run([str(tool), '--version'], capture_output=True, text=True, check=True)
    require(source_lock()['lean_revision'] in result.stdout, 'Compiler revision differs: ' + result.stdout)
    require((directory / 'leanchecker').is_file(), 'Missing paired leanchecker')
    return directory

def fresh_run(prefix):
    parent = ROOT / '.runs'
    parent.mkdir(exist_ok=True)
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    return Path(tempfile.mkdtemp(prefix=prefix + '-' + stamp + '-', dir=parent))

def lean_env(bindir, packages, objects, scratch):
    env = os.environ.copy()
    for key in ['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT']:
        env.pop(key, None)
    search = [objects] + [Path(packages) / p['name'] / '.lake/build/lib/lean'
                          for p in source_lock()['packages']] + [bindir.parent / 'lib/lean']
    env.update(LEAN_PATH=os.pathsep.join(map(str, search)),
               PATH=str(bindir) + os.pathsep + env.get('PATH', ''),
               TMPDIR=str(scratch), TMP=str(scratch), TEMP=str(scratch),
               LAKE_NO_CACHE='1', MATHLIB_NO_CACHE_ON_UPDATE='1')
    return env

def imports(path):
    """Read the fixed inventory's simple Lean headers, ignoring nested comments."""
    source = path.read_text()
    clean, depth, i = [], 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if source[i] == '\n':
                clean.append('\n')
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else:
            clean.append(source[i])
            i += 1
    require(depth == 0, 'Unclosed Lean comment')
    result = []
    for line in ''.join(clean).splitlines():
        line = line.strip()
        if not line or line in {'module', 'prelude'}:
            continue
        match = re.fullmatch(r'(?:(?:public|meta)\s+)*import\s+(.+)', line)
        if match:
            names = match[1].split()
            require(all(NAME.fullmatch(n) for n in names), 'Unsupported import header')
            result.extend(names)
        else:
            require(line != 'import', 'Unsupported multiline import')
            break
    return result

def module_order(manifest):
    available = {p[5:-5].replace('/', '.'): ROOT / p for p in manifest['sha256']}
    order, done, active = [], set(), set()
    def visit(name):
        if name in done:
            return
        require(name not in active, 'Cyclic local imports')
        active.add(name)
        for dependency in imports(available[name]):
            if dependency in available:
                visit(dependency)
            elif dependency.startswith(('ReyZygmund.', 'Verification.')):
                raise ValueError('Missing local dependency: ' + dependency)
        active.remove(name)
        done.add(name)
        order.append(name)
    for name in sorted(available):
        visit(name)
    return order

def control_hashes():
    paths = [ROOT / 'tools' / name for name in ['common.py', 'check.py']]
    paths += [ROOT / p for p in ['verification/TARGETS.json', 'verification/SOURCE-MANIFEST.json',
                                'verification/AUDIT-MANIFEST.json',
                                'lean/SOURCE_LOCK.json', 'lean/lean-toolchain',
                                'lean/lake-manifest.json', 'lean/lakefile.toml']]
    return {str(p.relative_to(ROOT)): digest(p) for p in paths}
