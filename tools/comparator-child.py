#!/usr/bin/env python3
"""Pinned bundled Comparator invocation inside its resource unit. Apache-2.0."""
import json
from pathlib import Path
import subprocess
import sys

lake, config = sys.argv[1:]
cfg=json.loads(Path(config).read_text())
if set(cfg.get('external_kernels',{})) != {'nanoda','con-ron'}:
    raise SystemExit('Both independent kernels are required')
group=next(line.split('::',1)[1] for line in Path('/proc/self/cgroup').read_text().splitlines() if line.startswith('0::'))
cg=Path('/sys/fs/cgroup'+group)
if (cg/'memory.max').read_text().strip()!=str(6*1024**3) or (cg/'memory.swap.max').read_text().strip()!='0':
    raise SystemExit('Expected actual 6 GiB and zero-swap limits')
print('PASS actual cgroup limits and both required external kernels',flush=True)
result=subprocess.run([lake,'comparator','--config',config])
print('FINAL_CGROUP '+json.dumps({n:(cg/n).read_text().strip() for n in ('memory.peak','memory.events','cpu.stat')}),flush=True)
raise SystemExit(result.returncode)
