# Linux checker setup

This guide gives the sandboxed Linux procedure for checking the three main
and nineteen selected supporting results with Comparator, Lean, Nanoda and con-ron,
under the same checking standard. It assumes you can create a Linux virtual
machine or use an existing Linux computer and install system software. The
[verification guide](../VERIFYING.md) explains the tools and offers
[local macOS checking](../VERIFYING.md#local-checking-on-macos) as an alternative.

**Follow steps 1–4 in order, using a terminal inside Linux throughout.** First
prepare the system and tools; then obtain the repository, prepare its libraries
and run the checks. Wait for each command to finish successfully before
continuing. You do not need to switch back to the verification guide.

Before running the checks, read the
[independent statements and their definitions](../lean/ReyZygmund/MathlibOnly/README.md)
to assess whether they express the mathematics you want to verify. This
procedure uses `lake comparator` bundled with Lean **4.35.0-rc4** and its
**bubblewrap** sandbox, following the
[documentation for that version](https://github.com/leanprover/lean4/blob/c29b6dda4f7c20e3eeaa717c4e565663c5cfa364/src/lake/Lake/CLI/Help.lean#L403-L499).

<a id="choose-a-clean-checking-environment"></a>
<a id="install-the-pinned-tools"></a>
<a id="2-install-lean-the-libraries-and-the-sandbox"></a>

## 1. Prepare Linux and install the tools

We recommend a fresh Linux VM from a trusted image. Once it is running,
open its Linux terminal. A correctly configured Linux computer also works.
Use an ordinary user account for the checks; administrator privileges are
needed only to install system packages and adjust the settings below.
There is no need to clone the project yet.

The system needs user-level systemd, cgroup v2 and support for unprivileged
user namespaces. Install these prerequisites from trusted sources:

- Python 3.12 or later, Git and `curl`.
- A C compiler available as `cc`, with static C-library support for the
  small test programs.
- [elan](https://github.com/leanprover/elan), the Lean toolchain manager.
- **bubblewrap 0.12.0**. If your distribution does not provide this version,
  use its [official source-build instructions](https://github.com/containers/bubblewrap/blob/v0.12.0/README.md#installation).
  Building it requires Meson, Ninja, pkg-config and libcap development headers
  in addition to the C compiler. [CHECKER-PINS.json](CHECKER-PINS.json) records
  the source archive and its checksum; verify the checksum before building.

Install Lean and confirm the bubblewrap installation:

```sh
elan toolchain install leanprover/lean4:v4.35.0-rc4
bwrap --version
command -v bwrap
```

Lean includes Comparator, its proof exporter, and all three proof checkers.
The second command must print `bubblewrap 0.12.0`; keep the executable path
printed by the third command for step 2. No mock sandbox or sandbox-disabling
option is used in this procedure.

Check that the user-level system service is available and inspect the
memory-mapping limit:

```sh
systemctl --user show-environment
sysctl vm.max_map_count
```

The first command must succeed. Use a memory-mapping limit of at least
262144 for this procedure. If the second command reports a lower value,
an administrator can raise it:

```sh
sudo sysctl -w vm.max_map_count=262144
```

For a VM, we recommend four virtual CPU cores and 8 GiB of memory. The twenty-two
cases run one at a time, each limited to 6 GiB without swap, leaving memory
for Linux itself. Allow at least 15 GiB of free disk space for working copies
after installing the tools and libraries.

<a id="1-enter-linux-and-obtain-the-repository"></a>

## 2. Obtain the repository and register the tools

Now clone the repository inside Linux:

```sh
git clone https://github.com/hjmartik/ZygmundConjecture.git
cd ZygmundConjecture
git rev-parse HEAD
```

Record the commit printed by the last command. A fresh clone supplies the
sources without compiled project files. Do not add `.lake`, `.runs` or
`.tools` directories from another installation.

**Run every remaining repository command from this directory.** It contains
`README.md`, `tools/` and `lean/`. There is no need to enter `lean/` or the
working copies created by the checking programs.

Before running repository scripts, inspect the checking scripts, Lake
configuration, dependency manifest, and challenge files with their imports.
These are trusted inputs to the procedure. The twenty-two challenges import the
independent `Statements.lean` or `SupportingStatements.lean`, together with
their definition modules. These five specification modules use Mathlib without
importing the proof library. The configurations select the twenty-two targets and
the three permitted foundational axioms.
[SOURCE-MANIFEST.json](SOURCE-MANIFEST.json) and
[AUDIT-MANIFEST.json](AUDIT-MANIFEST.json) identify the source and adapter
files; the runner checks them against these inventories.

Do not run an ordinary project build, `tools/check.py verify`, or the Lean
inspection tests in this environment before Comparator. Nor should you open
the files in a Lean-enabled editor that automatically processes them. Read
the source as text or through the published source pages. The project proofs
will first be compiled inside Comparator's sandbox.

Register the tools installed in step 1:

```sh
python3 -I -B tools/install-checkers.py --bwrap /absolute/path/to/bwrap
```

Replace the placeholder with the bubblewrap path you recorded. The command
checks the tool versions, copies bubblewrap into `.tools/checkers` and records
executable hashes. It does not download or install missing tools, authenticate
an arbitrary binary's origin, or check proofs.

Some Linux systems require permission for this copied executable to create
a sandbox. Check whether AppArmor's user-namespace restriction is enabled:

```sh
sysctl -n kernel.apparmor_restrict_unprivileged_userns
```

If it prints `1`, complete the
[path-specific setup below](#if-apparmor-restricts-bubblewrap) before step 3.
If it prints `0`, or reports that this setting does not exist, continue to
step 3. This permission depends on the repository's location, so it is
configured after cloning. The setup tests in step 3 must still pass.

<a id="check-the-runtime"></a>
<a id="3-test-the-checking-environment"></a>

## 3. Prepare the libraries and test the setup

Download the background-library sources and their compiled files:

```sh
python3 -I -B tools/dependencies.py fetch
python3 -I -B tools/dependencies.py cache
```

The scripts select the Lean version from `lean/lean-toolchain`; no change
to elan's global default is needed. They verify the library source archives,
build Mathlib's cache utility using the reviewed Lake configuration, and obtain
the matching compiled files from `cache.mathlib.org`. This saves building
the background libraries. It does not compile the project proofs.

This setup trusts those upstream sources and the official compiled cache.
Keep the recorded versions; do not replace these commands with `lake update`.

Next, test the checking environment:

```sh
python3 -I -B tools/test_comparator_runtime.py
```

These eight small examples include a valid proof and deliberately invalid
cases: changed statements or definitions, an indirect admission, and missing
or failing checkers. They exercise the same sandbox and checking programs as
the main run without compiling the project proofs or changing its configurations.

Continue only if the command exits successfully and its report says
**`PASS_FIXTURES_ONLY`**. A sandbox error is not a successful negative test;
resolve setup failures before proceeding.

<a id="check-the-main-results"></a>

## 4. Run Comparator on all twenty-two results

The tools and libraries are now installed and the setup tests have passed.
The project proofs have not yet been compiled. From the same repository
directory inside Linux, run:

```sh
python3 -I -B tools/comparator.py
```

This command prepares its own source-only working copy, compiles the project
inside the sandbox, and compares all twenty-two results with their independent
specifications. No separate preparation command or ordinary build is needed.

Success requires the command to exit successfully and **`PASS_ALL_TWENTY_TWO`** in
the report whose path it prints. For each result, that requires successful
Comparator comparison and explicit acceptance by Lean, Nanoda and con-ron.
A partial or failed run does not verify all twenty-two results.

Each case has a two-core CPU quota and a one-hour limit. A timeout fails the
run; it is not a mathematical rejection. Before reporting success, the runner
rechecks the identities of the sources, libraries, configurations and tools.

Keep the complete `.runs/comparator-*/` result directory, including its
`report.json` and logs, together with the repository commit and the setup-test
reports. The [verification guide](../VERIFYING.md) explains the mathematical
coverage and the optional broader checks.

## What the sandbox protects

The Linux checking scripts automatically place each comparison in an outer
bubblewrap sandbox, using the executable registered in step 2. It keeps
checking offline and makes the filesystem read-only except for the run's
working directories. Inside it, Comparator additionally sandboxes
configuration evaluation, compilation, proof export and external checker
execution. Its inner sandbox protects source files and hides the user's
home. Comparator does not load the project's compiled Lean files into the
process deciding the verdict. The outer network restriction also covers
dependency resolution.

These restrictions reduce trust in the proof library's executable code.
They do not remove the need to assess the independent specification or to
trust the system image, tools, background libraries and checking scripts.

## If AppArmor restricts bubblewrap

On systems with this restriction, an administrator must authorize the
**registered executable's path**, not just the original installation. From
the repository directory, obtain that path:

```sh
realpath .tools/checkers/bwrap
```

Use the resulting absolute path in this profile:

```text
abi <abi/4.0>,
include <tunables/global>
profile zygmund-comparator-bwrap /absolute/path/to/repository/.tools/checkers/bwrap flags=(unconfined) {
  userns,
}
```

An administrator can save it as `/etc/apparmor.d/zygmund-comparator-bwrap`
and load it with:

```sh
sudo apparmor_parser -r /etc/apparmor.d/zygmund-comparator-bwrap
```

This grants namespace permission to that executable; bubblewrap still
enforces the checker sandbox. Do not disable the system-wide restriction or
run the checker as root. Once the profile is loaded, continue with step 3.

## Alternative tool locations

The numbered procedure uses elan and keeps the downloaded libraries inside
this repository. No extra options are needed for that route.

If using an extracted official Lean archive instead of elan,
[CHECKER-PINS.json](CHECKER-PINS.json) records the version and the official
Linux ARM64 archive URL and SHA-256. Verify that checksum before using the
archive; other architectures need their corresponding official release. Append
`--lean-bin /absolute/path/to/lean/bin` to the `install-checkers.py`,
`dependencies.py cache`, `test_comparator_runtime.py` and `comparator.py`
commands, using the archive's extracted `bin` directory.

The runner's `--packages` option can select a separately provisioned pinned
dependency tree. Use libraries obtained from trusted sources, not from a
potentially compromised environment.
