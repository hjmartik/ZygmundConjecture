#!/usr/bin/env python3
"""Register bundled rc4 checkers and an existing pinned bubblewrap. Apache-2.0.

No downloads, source builds, privilege changes or implicit dependency updates.
"""
import argparse
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from common import ROOT,compiler_bin,read_json,require,digest,fresh_run,write_json
from comparator import tool_paths

def main(args):
    require(platform.system()=='Linux' and os.geteuid()!=0,'Use an unprivileged Linux user')
    bindir=compiler_bin(args.lean_bin)
    source=args.bwrap.expanduser().resolve(strict=True)
    pins=read_json(ROOT/'verification/CHECKER-PINS.json')
    require(subprocess.check_output([source,'--version'],text=True).strip()=='bubblewrap '+pins['bubblewrap']['version'],
            'Bubblewrap version differs')
    destination=ROOT/'.tools/checkers';destination.mkdir(parents=True,exist_ok=True)
    target=destination/'bwrap'
    if target.exists():require(not target.is_symlink() and digest(target)==digest(source),'Existing bubblewrap differs; keep it and use --tools with another directory')
    else:shutil.copy2(source,target)
    bins=tool_paths(destination,bindir)
    run=fresh_run('checker-setup')
    write_json(run/'receipt.json',dict(status='TOOLS_PRESENT_NOT_PROOFS_CHECKED',pins=pins,
        tools={n:dict(path=str(p),sha256=digest(p)) for n,p in bins.items()},network=False,
        bubblewrap_source_archive_verification='Not performed by this registration command'))
    print('PASS required tools present; runtime and proof checks are separate. Receipt: '+str(run/'receipt.json'))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bwrap',type=Path,required=True,help='Existing bubblewrap 0.12.0 executable')
    parser.add_argument('--lean-bin')
    main(parser.parse_args())
