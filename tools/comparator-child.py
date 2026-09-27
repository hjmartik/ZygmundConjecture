#!/usr/bin/env python3
"""Comparator invocation inside its Linux resource unit. Apache-2.0."""
import json
import os
from pathlib import Path
import subprocess
import sys

lake, comparator, config = sys.argv[1:]
if json.loads(Path(config).read_text()).get('enable_nanoda') is not True:
    raise SystemExit('Nanoda is required')
group = next(line.split('::', 1)[1] for line in Path('/proc/self/cgroup').read_text().splitlines()
             if line.startswith('0::'))
cg = Path('/sys/fs/cgroup' + group)
if (cg / 'memory.max').read_text().strip() != str(6 * 1024**3) or (cg / 'memory.swap.max').read_text().strip() != '0':
    raise SystemExit('Expected actual 6 GiB / zero-swap cgroup limits')
if not Path(os.environ['TMPDIR']).resolve().is_relative_to(Path.cwd().resolve() / '.lake'):
    raise SystemExit('Scratch directory must be inside packet .lake')
print('PASS actual cgroup limits and required Nanoda', flush=True)
result = subprocess.run([lake, 'env', comparator, config])
print('FINAL_CGROUP ' + json.dumps({name: (cg / name).read_text().strip()
                                  for name in ['memory.peak', 'memory.events', 'cpu.stat']}), flush=True)
raise SystemExit(result.returncode)
