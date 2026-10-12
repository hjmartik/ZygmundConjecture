#!/usr/bin/env python3
"""Check the actual outer sandbox before a comparison. Apache-2.0."""
import errno
import os
from pathlib import Path
import sys

sentinel, parent_network=sys.argv[1:]
if os.readlink('/proc/self/ns/net')==parent_network:
    raise SystemExit('Network namespace was not isolated')
try:
    with Path(sentinel).open('a') as stream: stream.write('UNEXPECTED WRITE\n')
except OSError as error:
    if error.errno not in (errno.EROFS,errno.EACCES,errno.EPERM):raise
else:raise SystemExit('Outside-packet write was not denied')
probe=Path(os.environ['TMPDIR'])/'preflight-allowed.txt'
with probe.open('x') as stream:stream.write('allowed\n')
if probe.read_text()!='allowed\n':raise SystemExit('Permitted scratch write failed')
print('PASS isolated network namespace, outside-packet write denial, scratch write')
