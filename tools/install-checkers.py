#!/usr/bin/env python3
"""Explicit Linux software provisioning; not proof acceptance. Apache-2.0."""
import os
from pathlib import Path
import platform
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import ROOT, require, read_json, compiler_bin, fresh_run, digest, write_json

def main():
    require(platform.system() == 'Linux' and os.geteuid() != 0, 'Use an unprivileged Linux user')
    pins = read_json(ROOT / 'verification/CHECKER-PINS.json')
    bindir = compiler_bin()
    destination = ROOT / '.tools/checkers'
    destination.mkdir(parents=True, exist_ok=True)
    report = fresh_run('install-checkers')
    env = os.environ.copy()
    env['PATH'] = str(bindir) + os.pathsep + env.get('PATH', '')
    env.update(LAKE_NO_CACHE='1', MATHLIB_NO_CACHE_ON_UPDATE='1',
               TMPDIR=str(report), TMP=str(report), TEMP=str(report))
    steps = []
    def call(args, cwd=destination):
        args = list(map(str, args))
        log = report / f'{len(steps):02d}.log'
        with log.open('w') as output:
            result = subprocess.run(args, cwd=cwd, env=env, stdout=output, stderr=subprocess.STDOUT)
        steps.append(dict(args=args, log=log.name, exit_code=result.returncode))
        write_json(report / 'steps.json', steps)
        require(result.returncode == 0, 'Setup failed; inspect ' + str(log))
    def checkout(name, path):
        item = pins[name]
        if not path.exists():
            path.mkdir(parents=True)
            call(['git', 'init', str(path)])
            call(['git', '-C', path, 'fetch', '--depth=1', item['repository'], item['commit']])
            call(['git', '-C', path, 'checkout', '--detach', item['commit']])
        revision = subprocess.run(['git', '-C', str(path), 'rev-parse', 'HEAD'],
                                  check=True, capture_output=True, text=True).stdout.strip()
        require(revision == item['commit'], 'Existing checker has a different revision: ' + name)
        status = subprocess.run(['git', '-C', str(path), 'status', '--porcelain', '--untracked-files=no'],
                                check=True, capture_output=True, text=True).stdout.strip()
        require(not status, 'Existing tracked checker edits: ' + name)
    comparator = destination / 'comparator'
    checkout('comparator', comparator)
    checkout('lean4export', comparator / '.lake/packages/lean4export')
    call([bindir / 'lake', '--no-cache', 'build', 'lean4export', 'comparator'], cwd=comparator)
    checkout('landrun', destination / 'landrun')
    call(['go', 'build', '-trimpath', '-o', 'landrun', '.'], cwd=destination / 'landrun')
    checkout('nanoda', destination / 'nanoda')
    call(['cargo', 'build', '--release', '--locked'], cwd=destination / 'nanoda')
    from comparator import tool_paths
    bins = tool_paths(destination, bindir)
    write_json(report / 'receipt.json', {'status': 'TOOLS_BUILT_NOT_PROOFS_CHECKED', 'pins': pins,
                                       'binary_sha256': {name: digest(path) for name, path in bins.items()}})
    print('Pinned tools built. Runtime preflight and proof checks remain separate.')
    print('Receipt: ' + str(report / 'receipt.json'))

if __name__ == '__main__':
    main()
