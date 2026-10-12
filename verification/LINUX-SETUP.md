# Linux checker setup

Use an unprivileged Linux account with Python 3.12+, user-level systemd,
cgroup v2 and working bubblewrap namespaces. The recorded checks used Linux
ARM64. A Linux VM is suitable on macOS; no host home-directory mount is needed.

## Install the pinned tools

Install the official Lean **4.35.0-rc4** toolchain and pinned dependencies as
described in [the verification guide](../VERIFYING.md). This toolchain bundles Comparator,
`leanexport`, `leanchecker`, `nanoda_bin` and `con-ron`.

Supply **bubblewrap 0.12.0** from a trusted installation. Its official source
archive and SHA-256 are recorded in [CHECKER-PINS.json](CHECKER-PINS.json).
For a source build, obtain that exact archive, verify its checksum and follow
the instructions included with it. Do not substitute a mock sandbox.

From the repository root, register the installed executable:

```sh
python3 -I -B tools/install-checkers.py --bwrap /path/to/bwrap
```

Replace the example path with the actual executable. The command checks the
version and bundled tools, copies bubblewrap into `.tools/checkers` without
replacing a different installation, and records hashes. It does not download,
build software, authenticate an arbitrary binary's provenance or check proofs.
Use `--lean-bin /path/to/lean/bin` if elan does not select the installed compiler.

## Check the runtime

Confirm that `systemctl --user show-environment` works. The exporter may require
a higher memory-mapping limit; the recorded environment used 262144. If needed,
an administrator can set this explicitly:

```sh
sudo sysctl -w vm.max_map_count=262144
```

The checking process itself must not run as root. Its outer bubblewrap sandbox
isolates the network and makes the filesystem read-only except for its working
directories. Comparator additionally applies its own build/export sandbox.

```sh
python3 -I -B tools/test_comparator_runtime.py
```

These tiny fixtures require a C compiler available as `cc`, with static libc support for the
deliberately failing executable. They include three-kernel success, statement
and definition mismatches, an indirect admission, missing checkers and actual
checker-process failures. They do not change production configurations.

## Check the main results

```sh
python3 -I -B tools/comparator.py --prepare-only
python3 -I -B tools/comparator.py
```

Preparation does not check proofs. The full command compares all six results
and requires actual Lean, Nanoda and con-ron acceptance. Only `PASS_ALL_SIX`
records full-suite success. Optional `--case 6` checks just the sharpness export
and can produce only `PASS_ONE_CASE_ONLY`.

Each case is bounded to 6 GiB of memory, no swap, two CPU cores' worth of quota
and one hour. A timeout fails the run; it is not a mathematical rejection.
Keep at least 15 GiB free for working copies, in addition to installed tools
and dependencies; the actual requirement depends on cache and filesystem sizes.

The runner operates offline after provisioning. `--packages` selects an
existing pinned archive-backed dependency tree, copied before compilation.
`--tools` selects another directory containing bubblewrap. Logs, commands,
resolved configurations and reports remain under `.runs/`.

Versions are fixed for this release, not resolved from current upstream branches.
The [verification guide](../VERIFYING.md) explains scope and acceptance.
