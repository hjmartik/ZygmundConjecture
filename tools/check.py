#!/usr/bin/env python3
"""Fresh 453-contract verification or ordinary replay. SPDX-License-Identifier: Apache-2.0"""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import (ROOT, LEAN, ALLOW, require, digest, read_json, write_json, source_manifest,
                    targets, check_dependencies, compiler_bin, fresh_run, lean_env,
                    module_order, control_hashes)

def inspect_reports(output, selected):
    rows = [json.loads(line[len('RZ_REPORT '):]) for line in output.splitlines()
            if line.startswith('RZ_REPORT ')]
    require(len(rows) == len(selected) and len({r['target'] for r in rows}) == len(rows),
            'Missing or duplicated inspector reports')
    by_name = {r['target']: r for r in rows}
    require(set(by_name) == {t['name'] for t in selected}, 'Inspector selection differs')
    for t in selected:
        r = by_name[t['name']]
        require(r['matches'] is True, 'Contract mismatch: ' + t['name'])
        require(r['contract'] == t['contract'] and r['module'] == t['module']
                and r['contract_module'] == t['contract_module'], 'Wrong declaration origin')
        require(set(r['axioms']) <= ALLOW, 'Unapproved axiom: ' + t['name'])
    return rows

class Run:
    def __init__(self, kind, bindir, packages, objects=None):
        self.path = fresh_run(kind)
        self.objects = objects or self.path / 'objects'
        if objects is None:
            self.objects.mkdir()
        self.env = lean_env(bindir, packages, self.objects, self.path)
        self.record = dict(status='RUNNING', mode=kind, started_utc=datetime.now(timezone.utc).isoformat(),
                           commands=[], dependency_cache_reused=True,
                           semantic_correspondence='Separate human/mathematical review',
                           comparator='NOT_RUN', nanoda='NOT_RUN')
        print('Run: ' + str(self.path), flush=True)

    def save(self):
        write_json(self.path / 'report.json', self.record)

    def command(self, args, cwd=LEAN, timeout=1200, warnings=False):
        args = list(map(str, args))
        index = len(self.record['commands'])
        logfile = self.path / f'{index:03d}.log'
        started = time.monotonic()
        try:
            result = subprocess.run(args, cwd=cwd, env=self.env,
                                    capture_output=True, text=True, timeout=timeout)
            output, code = result.stdout + result.stderr, result.returncode
        except subprocess.TimeoutExpired as failure:
            def decode(s):
                return s.decode(errors='replace') if isinstance(s, bytes) else s or ''
            output, code = decode(failure.stdout) + decode(failure.stderr), None
        logfile.write_text(output)
        self.record['commands'].append(dict(args=args, exit_code=code,
                                           seconds=round(time.monotonic()-started, 3),
                                           log=logfile.name, log_sha256=digest(logfile)))
        self.save()
        require(code == 0, 'Command failed/timed out; see ' + str(logfile) + '\n' + output[-1800:])
        require(warnings or 'warning:' not in output, 'Compiler warning; see ' + str(logfile))
        return output

def object_hashes(objects, modules):
    result = {}
    for module in modules:
        path = objects / (module.replace('.', '/') + '.olean')
        require(path.is_file(), 'Missing local object: ' + module)
        require(not Path(str(path) + '.server').exists() and not Path(str(path) + '.private').exists(),
                'Unexpected local object sidecar: ' + module)
        result[module] = digest(path)
    return result

def execute(args):
    manifest = source_manifest()
    selected = targets()
    packages = (args.packages or LEAN / '.lake/packages').expanduser().resolve()
    pins = check_dependencies(packages)
    bindir = compiler_bin(args.lean_bin)
    modules = module_order(manifest)
    controls = control_hashes()
    tool_hashes = {name: digest(bindir / name) for name in ['lean', 'leanchecker']}
    previous = None
    if args.mode == 'replay':
        require(args.run is not None, 'replay requires --run PATH-TO-ROUTINE-REPORT')
        previous = read_json(args.run)
        require(previous['status'] == 'PASS' and previous['mode'] == 'verify', 'Need a successful routine run')
        require(previous['controls'] == controls and previous['source_files'] == manifest['sha256'],
                'Routine inputs have changed')
        require(previous['tool_sha256'] == tool_hashes and previous['dependency_sources'] == pins,
                'Routine compiler or dependency identity differs')
        objects = args.run.resolve().parent / 'objects'
        require(object_hashes(objects, modules) == previous['object_sha256'], 'Routine objects have changed')
        run = Run('replay', bindir, packages, objects)
        run.record.update(routine_sha256=digest(args.run),
                          exclusions='unsafe and partial constants (ordinary leanchecker behavior)',
                          independent_kernel=False, dependency_replay=False)
    else:
        require(args.run is None, '--run is only for replay')
        run = Run('verify', bindir, packages)
    run.record.update(source_files=manifest['sha256'], controls=controls, tool_sha256=tool_hashes,
                      dependency_sources=pins, lean_path=run.env['LEAN_PATH'],
                      local_module_count=len(modules), registered_declaration_count=len(selected))
    started = time.monotonic()
    try:
        if previous is None:
            for i, module in enumerate(modules, 1):
                relative = module.replace('.', '/')
                output = run.objects / (relative + '.olean')
                output.parent.mkdir(parents=True, exist_ok=True)
                run.command([bindir / 'lean', '-DautoImplicit=false', '-o', output, relative + '.lean'])
                print(f'Built {i}/{len(modules)}: {module}', flush=True)
            roots = sorted({d[k] for d in selected for k in ['module', 'contract_module']})
            text = '\n'.join('import ' + m for m in roots + ['Verification.Inspect']) + '\n\n'
            text += '\n'.join('#rz_verify ' + d['name'] + ' against ' + d['contract'] for d in selected) + '\n'
            inspector = run.path / 'InspectTargets.lean'
            inspector.write_text(text)
            output = run.command([bindir / 'lean', '-DautoImplicit=false', inspector], timeout=1800)
            reports = inspect_reports(output, selected)
            write_json(run.path / 'declarations.json', reports)
            run.record.update(fresh_project_rebuild=True, declarations_sha256=digest(run.path / 'declarations.json'),
                              object_sha256=object_hashes(run.objects, modules))
        else:
            for i, module in enumerate(modules, 1):
                output = run.command([bindir / 'leanchecker', '-v', module], cwd=run.path)
                reported = [line.removeprefix('replaying ') for line in output.splitlines()
                            if line.startswith('replaying ')]
                require(reported == [module], 'Replay did not report exactly the requested module')
                print(f'Replayed {i}/{len(modules)}: {module}', flush=True)
            require(object_hashes(run.objects, modules) == previous['object_sha256'], 'Objects changed during replay')
            require(digest(args.run) == run.record['routine_sha256'], 'Routine report changed during replay')
            run.record['object_sha256'] = previous['object_sha256']
        require(source_manifest() == manifest and control_hashes() == controls, 'Inputs changed during checking')
        require(check_dependencies(packages) == pins, 'Dependency sources changed during checking')
        require({n: digest(bindir / n) for n in tool_hashes} == tool_hashes, 'Compiler changed during checking')
        run.record['status'] = 'PASS'
    except BaseException as failure:
        run.record['status'] = 'FAIL'
        run.record['failure'] = str(failure)
        raise
    finally:
        run.record['seconds'] = round(time.monotonic()-started, 3)
        run.record['finished_utc'] = datetime.now(timezone.utc).isoformat()
        run.save()
    print('PASS: ' + str(run.path / 'report.json'), flush=True)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['verify', 'replay'])
    parser.add_argument('--lean-bin', help='Directory containing the exact Lean 4.34.0 tools; default: elan which lean')
    parser.add_argument('--packages', type=Path, help='Reuse an existing pinned archive-backed package directory, read-only')
    parser.add_argument('--run', type=Path, help='Successful routine report.json to replay')
    execute(parser.parse_args())
