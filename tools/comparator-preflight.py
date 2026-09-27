#!/usr/bin/env python3
"""Executed inside the resource-limited systemd unit. Apache-2.0."""
import ctypes
import errno
from pathlib import Path
import socket
import subprocess
import sys
import tempfile

project, landrun = Path(sys.argv[1]), sys.argv[2]
try:
    socket.socket(socket.AF_UNIX)
except OSError as failure:
    if failure.errno not in [errno.EAFNOSUPPORT, errno.EPERM, errno.EACCES]:
        raise
else:
    raise SystemExit('AF_UNIX restriction is not effective')
libc = ctypes.CDLL(None, use_errno=True)
abi = libc.syscall(444, 0, 0, 1)
if abi < 4:
    raise SystemExit('Landlock ABI insufficient: ' + str(abi))
root = Path(tempfile.mkdtemp(prefix='preflight-', dir=project / '.lake/verification-tmp'))
(root / 'allowed').mkdir()
(root / 'protected.txt').write_text('preserve\n')
probe = '''import errno, pathlib, socket, sys
root = pathlib.Path(sys.argv[1])
(root / 'allowed/inside.txt').write_text('allowed')
try: (root / 'protected.txt').write_text('not allowed')
except OSError as e:
    if e.errno not in [errno.EPERM, errno.EACCES]: raise
else: raise SystemExit('Protected file writable')
if (root / 'protected.txt').read_text() != 'preserve\\n': raise SystemExit('Protected file changed')
s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
try: s.bind(('127.0.0.1', 0))
except OSError as e:
    if e.errno not in [errno.EPERM, errno.EACCES]: raise
else: raise SystemExit('TCP bind not denied')
'''
subprocess.run([landrun, '--best-effort', '--ro', '/', '--rw', '/dev', '--rwx', str(root / 'allowed'),
                '-ldd', '-add-exec', '--', sys.executable, '-c', probe, str(root)], check=True)
print(f'PASS actual AF_UNIX restriction; Landlock ABI {abi}; permitted write, denied write, denied TCP bind')
