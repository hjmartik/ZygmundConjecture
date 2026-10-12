# Checking the formalization

Choose the level of inspection you want:

- **Read the mathematics and inspect its formulation.** Start with
  [Main theorems](MAIN-STATEMENTS.md), then follow the links beneath a theorem
  to its independent Lean statement and definitions. The
  [consistency guide](CONSISTENCY.md) explains the mathematical objects and
  the identifications used. This requires no installation of Lean or Linux.
- **Compile and check with Lean.** Follow
  [dependency setup](#1-install-the-pinned-dependencies) and
  [build and statement inspection](#2-build-and-check-all-registered-declarations).
  [Ordinary kernel replay](#3-ordinary-kernel-replay) is a further check with
  Lean's own checker.
- **Repeat the Comparator and independent-kernel checks.** Follow
  [the Linux instructions](#4-comparator-with-lean-nanoda-and-con-ron-on-linux)
  to compare the six independently stated results and check their exported
  proofs with Lean's default kernel, Nanoda and con-ron.

The next sections describe the mathematical scope and the completed checks.
The numbered instructions then explain how to reproduce them.

## Mathematical scope

[Main theorems](MAIN-STATEMENTS.md) gives the six results, including their
hypotheses, parameter ranges and cube conventions. The maximal and sparse
overlap estimates are stated for weakly incomparable families. The formalization
also retains a stronger, quantified form of the paper's sharpness remark for
the classical dyadic Zygmund family, as explained there.

The examples cited in the paper to establish sharpness of the incomparable
maximal power are not formalized.

The previous version of this repository presented seven main theorems. The
current version presents six: the estimates under weaker containment are
incorporated into the general statements for weakly incomparable families.
No mathematical coverage has been removed.

## What has been checked

The recorded runs cover **377 local modules and 497 registered declarations**.
A declaration is a named definition or theorem in Lean. The source inventory
contains 391 Lean files; the build and replay
selection excludes negative-test fixtures and other files outside its import
closure. This coverage combines earlier full local checks with checks of the
revised definitions, proofs and affected imports. The earlier checks still apply
to unchanged source files and their unchanged dependencies.

| Check | Recorded outcome and scope |
| --- | --- |
| Compilation | All 377 selected local modules compiled. |
| Statement and axiom inspection | All registered declarations matched their separately written formal statements and used only the permitted axioms. |
| Ordinary Lean replay | Completed for the 377 selected local modules, subject to the checker exclusions described in [step 3](#3-ordinary-kernel-replay). |
| Comparator, Lean, Nanoda and con-ron | All six comparisons against the independent specification rebuilt from Mathlib primitives passed, and all three kernels accepted the exported proofs and their exported dependencies. |

The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.
The six-result checks do not give independent-kernel coverage to every supporting
result; [step 4](#4-comparator-with-lean-nanoda-and-con-ron-on-linux) records the
precise scope.

The distributed Lean code matches the checked code exactly apart from comments.
The source hashes are listed in
[SOURCE-MANIFEST.json](verification/SOURCE-MANIFEST.json).
[RESULTS.json](verification/RESULTS.json) records the checks for this release,
including target identities, execution dates, tool hashes and the comment-only
source reconciliation.

The root file `PUBLIC-FILES.sha256` lists SHA-256 checksums for the other
distributed files.

Tests of the checking programs are a separate matter: they test whether the
programs accept valid inputs, reject deliberately invalid ones, and recover
missing compiled dependencies. Those tests are documented in
[PACKAGING-TESTS.md](verification/PACKAGING-TESTS.md). The instructions below
reproduce the mathematical checks summarized here.

## 1. Install the pinned dependencies

Use Python 3.12 or later, `curl`, Git, and [elan](https://github.com/leanprover/elan)
with Lean **4.35.0-rc4** installed. Run commands below from the repository root.

```sh
elan toolchain install leanprover/lean4:v4.35.0-rc4
python3 -I -B tools/dependencies.py fetch
python3 -I -B tools/dependencies.py cache
```

These are explicit network/setup operations. The first Python command obtains
nine fixed source archives and verifies their checksums. The second builds
Mathlib's official cache utility and obtains matching compiled dependencies
from `cache.mathlib.org`. Dependencies retain their upstream licenses.

The archive-backed layout is deliberate: [SOURCE_LOCK.json](lean/SOURCE_LOCK.json)
fixes commits, archive checksums and source-tree fingerprints. Do not replace
it with an unpinned `lake update`. This setup uses Mathlib's cache utility from
its own root to preserve cache identities with the downstream path manifest.

The dependency cache is architecture-specific. Do not copy macOS `.olean`
artifacts into the Linux checking environment. For missing cache items, see
[Troubleshooting dependency setup](#troubleshooting-dependency-setup).

## 2. Build and check all registered declarations

```sh
python3 -I -B tools/test_checker.py
python3 -I -B tools/test_inspection.py
python3 -I -B tools/check.py verify
```

The verifier checks all supplied Lean files and pinned dependency sources,
then builds the selected 377 local modules in import order into a fresh directory.
A **contract** is the separately written formal statement against which a
declaration is checked. [TARGETS.json](verification/TARGETS.json) lists the
declarations and their contracts.

The Lean inspector checks that each registered declaration's elaborated type
is definitionally equal to its contract. It uses full unfolding transparency,
allowing definitions to be unfolded in this comparison. Definitionally
identical presentations pass; propositions that are merely logically equivalent
do not pass on that basis. The inspector also checks axiom dependencies,
including those used indirectly through other declarations. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted.

The verifier rejects warnings, missing or mismatched declarations, unexpected
origins and any other axioms. It checks input identities again at completion.
It never uses an existing project object directory or starts a network download.

A successful run prints the path to its `report.json` under `.runs/`. A
nonzero exit or any status other than `PASS` is a failure, not partial acceptance.
The first two commands test the checking machinery. The cases for
`test_checker.py` are described in [Tests of the checking programs](verification/PACKAGING-TESTS.md),
and those for `test_inspection.py` under
[Testing the verification tools](#testing-the-verification-tools).

Advanced options for `check.py`: `--lean-bin` selects the exact installed compiler directory;
`--packages` reuses an existing archive-backed, pinned package directory
read-only. Defaults are the toolchain selected by `lean/lean-toolchain` and
`lean/.lake/packages`.

For editor navigation or ordinary incremental compilation, `cd lean` followed
by `lake build` builds the main-results entry point and its imports.
This is compilation, **not** the contract/axiom inspection above. Negative
fixtures and the external Comparator challenge adapters are not part of this
default build.

## 3. Ordinary kernel replay

Use the report path printed by step 2:

```sh
python3 -I -B tools/check.py replay --run .runs/VERIFY-RUN/report.json
```

Replace `VERIFY-RUN` with the run directory from step 2. If that step used
`--lean-bin` or `--packages`, use the same options here. Replay first compares
the source, object, dependency, control-file and tool identities with the
successful report from step 2. It then runs the paired `leanchecker -v MODULE` for
each selected local module. A **kernel** is the program that checks the resulting
formal proofs. This replay uses Lean's ordinary checker, not a second kernel,
and it does not replay every declaration in Mathlib. Its tool-level exclusions
are unsafe and partial constants.

<a id="4-comparator-with-nanoda-on-linux"></a>

## 4. Comparator with Lean, Nanoda and con-ron on Linux

For each result, a challenge file states the independently formulated theorem
without a proof, and a solution file supplies its proof from the library.
Comparator compares the theorem statements and the definitions on which they
depend, and checks the permitted axioms. Lean's default kernel, Nanoda and
con-ron check the exported proof.

The independent specification consists of
[Definitions.lean](lean/ReyZygmund/MathlibOnly/Definitions.lean),
[SubmittedDefinitions.lean](lean/ReyZygmund/MathlibOnly/SubmittedDefinitions.lean)
and [SubmittedStatements.lean](lean/ReyZygmund/MathlibOnly/SubmittedStatements.lean).
Their other imports are exclusively from Mathlib. They do not use proof-library
definitions, original contracts or solution modules.
The [independent specification guide](lean/ReyZygmund/MathlibOnly/README.md)
and [consistency guide](CONSISTENCY.md) explain the proved identities relating
these definitions to those used in the proofs.

The [comparison cases](verification/comparator/CASES.json) select the six
independently stated theorems and their proofs. The shared solution adapter
imports [SubmittedSolutions.lean](lean/ReyZygmund/MathlibOnly/SubmittedSolutions.lean),
where the library's results are connected to those statements.
[AUDIT-MANIFEST.json](verification/AUDIT-MANIFEST.json) records hashes
identifying the adapters, configurations, six-result mapping and
declaration/contract inventory.
The permitted axioms are the same three as in step 2.

Each `SubmittedChallengeN.lean` contains an intentional `sorry` placeholder
for the proof to be supplied by its solution. Isolated negative-test fixtures
also deliberately contain an admission or a custom axiom. Challenge adapters
are inventoried separately from the library; supplied negative fixtures are
outside the build/replay selection. Solutions cannot import either.

Use a regular, unprivileged Linux user, working user-level systemd, cgroup v2
and bubblewrap namespaces. On macOS, a Linux VM such as Lima supplies this
environment. The runner includes a sandbox preflight, network isolation and
bounded resources (6 GiB memory, no swap, a 200% CPU quota, one hour per case).

Install the same Lean and dependency sources/cache **inside Linux**, then
follow [Linux checker setup](verification/LINUX-SETUP.md) to register bubblewrap
and the checker tools bundled with Lean 4.35.0-rc4. The authoritative versions are in
[CHECKER-PINS.json](verification/CHECKER-PINS.json); do not substitute current
default branches.

The six configurations correspond to the
[weakly incomparable maximal estimate](verification/comparator/comparison-1.json),
[sparse weakly incomparable overlap estimate](verification/comparator/comparison-2.json),
[continuous Zygmund endpoint estimate](verification/comparator/comparison-3.json),
[rounded dyadic endpoint estimate](verification/comparator/comparison-4.json),
[sparse Φ-Zygmund overlap estimate](verification/comparator/comparison-5.json), and
[sharpness for the classical dyadic Zygmund family](verification/comparator/comparison-6.json).

```sh
python3 -I -B tools/comparator.py
```

To test the runner first, execute `python3 -I -B tools/test_comparator_runtime.py`
in this Linux environment; this test additionally requires a C compiler available
as `cc`, with static libc support. See [Testing the verification tools](#testing-the-verification-tools).

The runner first checks exact source, adapter and configuration identities. It
traverses the local imports of each challenge and solution: a challenge may
use only the three independent specification modules, while a solution must not
import any challenge placeholder or negative fixture. The imported dependency sources are checked
against their pins. These checks establish the source boundary, not the
mathematical faithfulness of the definitions.

For an offline packet and import-boundary check without invoking Linux tools:

```sh
python3 -I -B tools/comparator.py --prepare-only
```

Its status is `PREPARED_NOT_CHECKED`, never proof acceptance.

The full runner creates a fresh packet, copies the dependency tree, and checks all
six pairs sequentially. Acceptance requires a successful Comparator exit and
four explicit reports: successful comparison, Lean default-kernel acceptance,
Nanoda acceptance and con-ron acceptance. The runner records those observations
separately, checks inputs and tool hashes at the end, and retains reports and complete logs under
`.runs/`. Only
`PASS_ALL_SIX` means the complete suite passed. `--case 6` is an optional
single-result smoke test and can produce only `PASS_ONE_CASE_ONLY`.

All three kernels checked the six exported proofs and their exported
dependencies. Other supporting results have the ordinary Lean checks described
above; distribution in this repository does not by itself imply Nanoda or
con-ron coverage. These checks concern six exported theorems and their
dependencies, not a separate external comparison for every registered declaration.

Allow at least 15 GiB free guest disk for the runner, in addition to installed
tools and dependencies. Actual resource needs depend on the machine, caches
and filesystem.

## What remains trusted

Separate mathematical reviews compared the formal statements and definitions
with the paper, and checked the proofs relating the independent statements to
the library. This correspondence requires mathematical judgment: Comparator
compares formal statements, not the paper's text. Lean, Nanoda and con-ron
check the resulting proof terms. The permitted axioms, dependency sources and caches,
toolchain and operating environment are explicit parts of the setup. The checks
cover the six exported proofs and their exported dependencies, rather
than every result in the imported libraries.

## Troubleshooting dependency setup

If an official cache item is unavailable, recover it **offline from the
existing pinned sources**:

```sh
python3 -I -B tools/dependencies.py recover --module Mathlib.Analysis.SpecialFunctions.Log.Base
```

Use the module reported missing; `--module` may be repeated. Without it,
`recover` traverses the project's external import closure and builds missing
objects in dependency order. It preserves source pins, reuses complete cached
objects, and installs newly compiled artifacts only in dependency build caches.
It does not download, update dependencies, or invoke Lake build hooks. A
partial existing artifact is backed up in the new `.runs/` receipt directory
before replacement. `--packages PATH` selects an explicit pinned package tree
whose build cache you authorize the command to update; `--lean-bin` selects
the matching installed compiler.

For split modules, this direct-compiler workflow requires the full `.olean`,
`.olean.server`, `.olean.private`, `.ir.sig` and `.ir` family. Completeness is
checked before cache reuse, after compilation, and after installation; the
presence of the main `.olean` alone is not enough.

Source recovery can take longer than a cache download. A compiler failure
stops with a retained log. After `PASS_DEPENDENCY_RECOVERY`, rerun the failed
verification command. Recovery rebuilds dependency module artifacts, not
native dependency executables or widgets.

## Testing the verification tools

`test_inspection.py` compiles seven isolated Lean fixtures and uses the
production inspector and acceptance code: a valid theorem, a reducible
definitionally equal presentation, a merely logically equivalent presentation,
an indirect admission, a custom axiom, a changed conclusion and an extra
assumption. The first two pass; the remaining five are rejected. The valid
case also checks rejection of a wrong declaration origin.

To exercise dependency recovery itself, supply an existing complete pinned
cache to this optional isolated test:

```sh
python3 -I -B tools/test_recovery.py --packages lean/.lake/packages
```

It runs three isolated cases: the whole selected Mathlib artifact family
missing, only `.olean.server` missing, and only `.ir` missing while `.ir.sig`
remains. Each confirms an import failure, rebuilds from pinned source,
and verifies a small theorem through the production inspector. Retained
artifacts of the selected module are copied into scratch storage; other cached
objects are linked for read-only use. The original cache is not modified.

`test_comparator_runtime.py` runs a tiny Linux comparison with all three kernels,
then tests missing and deliberately failing Nanoda and con-ron executables.
In the failed-process cases, a regular static test executable must run, print
its invocation marker and exit nonzero while Lean and the other checker accept.
A sandbox failure to launch that executable does not satisfy this test.
The same acceptance function as the production runner must reject each failure.
The suite also tests an extra assumption, a changed definition and an indirect
admission. It requires a C compiler with static libc support; it never replaces
the installed checkers or edits the six production configurations.

`test_comparator_acceptance.py` tests report handling and runtime command
construction without executing a kernel. The actual completed tests are
summarized in [PACKAGING-TESTS.md](verification/PACKAGING-TESTS.md).

All fixture scripts retain reports with status `PASS_FIXTURES_ONLY`, distinct
from production acceptance. Scratch copies are left under `.runs/` for inspection.
