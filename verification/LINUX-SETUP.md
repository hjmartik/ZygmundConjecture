# Linux checker setup

This installs checking software, not mathematical dependencies; complete
steps 1–2 of [the verification guide](../VERIFYING.md) separately. Use a fresh
Linux environment if you need isolation from unrelated files. No host home
mount is required when using a VM.

Prerequisites are Lean 4.34.0, Python 3.12+, Git, a C/C++ toolchain, Go, Rust/Cargo,
and user-level systemd with cgroup v2. The known-working environment used
Ubuntu 26.04 ARM64, Go 1.26, Landlock ABI 8 and the exact revisions below.
Package installation is an explicit setup operation; the proof-checking runner
itself never installs software or downloads dependencies.

From the public repository root, after installing these prerequisites:

```sh
python3 -I -B tools/install-checkers.py
```

This fetches and builds the fixed revisions in
[CHECKER-PINS.json](CHECKER-PINS.json) into `.tools/checkers`, preserves existing
matching tool checkouts, and refuses different revisions or tracked edits.
It builds Comparator and lean4export with the pinned Lean version,
Landrun with Go, and Nanoda with `cargo build --release --locked`.
Git, Go and Cargo may download their declared software dependencies during
this setup. Nothing is installed system-wide, and no repository files are uploaded.

Then run, from a user session where `systemctl --user show-environment` works:

```sh
python3 -I -B tools/test_comparator_runtime.py
python3 -I -B tools/comparator.py --case 7
python3 -I -B tools/comparator.py
```

The first command tests the real runtime on five isolated fixtures: both
kernels accepting a valid theorem, missing Nanoda, failing Nanoda, a changed
referenced definition, and an indirect admission. It uses
a C compiler with static libc support to create the failing test executable;
no installed checker is replaced. Success is `PASS_FIXTURES_ONLY`.

The second command is optional and tests the sparse-family sharpness result.
Only the third checks all seven Mathlib-only main statements. Allow enough time and disk for
fresh project builds; dependencies may reuse their installed compatible caches.

Both source revisions and executable SHA-256 hashes are recorded. Source
revision checks alone do not authenticate an arbitrary prebuilt executable;
build the tools from the fixed checkouts in a trusted setup environment.
The initial checker tests included negative fixtures for altered statements,
extra assumptions, admissions, custom axioms, changed definitions and missing
targets. When run on a new machine, the runner tests effective Landlock/AF_UNIX restrictions
before invoking Comparator, and failures stop the run.

Upstream references: [Comparator](https://github.com/leanprover/comparator),
[lean4export](https://github.com/leanprover/lean4export),
[Landrun](https://github.com/Zouuup/landrun),
[Nanoda](https://github.com/ammkrn/nanoda_lib). Their source and license files
remain in the installed checkouts; they are not vendored into this repository.
