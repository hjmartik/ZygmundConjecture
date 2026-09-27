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
- **Repeat the Comparator and Nanoda checks.** Follow
  [the Linux instructions](#4-comparator-with-nanoda-on-linux) to compare the
  seven independently stated results and check their exported proofs with
  Lean's default kernel and Nanoda.

The next sections describe the mathematical scope and the completed checks.
The numbered instructions then explain how to reproduce them.

## Mathematical scope

[Main theorems](MAIN-STATEMENTS.md) gives the seven results, including their
hypotheses, parameter ranges and cube conventions. The sparse-family sharpness
theorem for the classical dyadic Zygmund family is included; it does not appear
in arXiv v1 and is intended for a subsequent revision. The examples cited in the
paper to establish sharpness of the incomparable maximal power are not formalized.

## What has been checked

The recorded runs completed the following checks on the development's
**363 local modules and 453 registered declarations**. A declaration is a
named definition or theorem in Lean.

| Check | Recorded outcome and scope |
| --- | --- |
| Compilation | All local modules compiled. |
| Statement and axiom inspection | All registered declarations matched their separately written formal statements and used only the permitted axioms. |
| Ordinary Lean replay | Completed for all local modules, subject to the checker exclusions described in [step 3](#3-ordinary-kernel-replay). |
| Comparator, Lean and Nanoda | All seven Mathlib-only statement comparisons passed, and both kernels accepted the exported proofs, including the declarations on which those proofs depend. |

The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.
The seven-result checks do not give Nanoda coverage to every supporting
result; [step 4](#4-comparator-with-nanoda-on-linux) records the precise scope.

The public source comments were subsequently edited for clarity. Comparison
with the checked sources confirmed that all code outside comments is unchanged,
including definitions, theorem statements and proofs. The mathematical checks
were not rerun for that editorial revision. The distributed sources and their
SHA-256 hashes are listed in [SOURCE-MANIFEST.json](verification/SOURCE-MANIFEST.json).

Tests of the checking programs are a separate matter: they test whether the
programs accept valid inputs, reject deliberately invalid ones, and recover
missing compiled dependencies. Those tests are documented in
[PACKAGING-TESTS.md](verification/PACKAGING-TESTS.md). The instructions below
reproduce the mathematical checks summarized here.

## 1. Install the pinned dependencies

Use Python 3.12 or later, `curl`, Git, and [elan](https://github.com/leanprover/elan)
with Lean **4.34.0** installed. Run commands below from the repository root.

```sh
elan toolchain install leanprover/lean4:v4.34.0
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

The verifier checks pinned dependency sources and builds all local modules
in import order into a fresh directory. A **declaration** is a named definition
or theorem in Lean; a **contract** is the separately written formal statement
against which it is checked. [TARGETS.json](verification/TARGETS.json) lists the
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
The first two commands test the checking machinery; their cases are described
under [Testing the verification tools](#testing-the-verification-tools).

Advanced options: `--lean-bin` selects the exact installed compiler directory;
`--packages` reuses an existing archive-backed, pinned package directory
read-only. Defaults are the toolchain selected by `lean/lean-toolchain` and
`lean/.lake/packages`.

For editor navigation or ordinary incremental compilation, `cd lean` followed
by `lake build` selects both local libraries. This is compilation, **not** the
contract/axiom inspection above. The external Comparator challenge adapters
are not part of this default build.

## 3. Ordinary kernel replay

Use the report path printed by step 2:

```sh
python3 -I -B tools/check.py replay --run .runs/VERIFY-RUN/report.json
```

Replace `VERIFY-RUN` with the run directory from step 2. If that step used
`--lean-bin` or `--packages`, use the same options here. Replay first compares
the source, object, dependency, control-file and tool identities with the
successful report from step 2. It then runs the paired `leanchecker -v MODULE` for
each local module. A **kernel** is the program that checks the resulting formal
proofs. This replay uses Lean's ordinary checker, not a second kernel,
and it does not replay every declaration in Mathlib. Its tool-level exclusions
are unsafe and partial constants.

Fresh build/inspection took about 20 minutes and ordinary replay about
42 minutes in the original environment. These are observations, not limits or
promises for other machines.

## 4. Comparator with Nanoda on Linux

For each result, a challenge file states the independently formulated theorem
without a proof, and a solution file supplies its proof from the library.
Comparator compares the theorem statements and the definitions on which they
depend, and checks the permitted axioms. Lean's default kernel and Nanoda check
the exported proof.

The independent specification consists of
[Definitions.lean](lean/ReyZygmund/MathlibOnly/Definitions.lean) and
[Statements.lean](lean/ReyZygmund/MathlibOnly/Statements.lean); their other
imports are exclusively from Mathlib. They do not use proof-library definitions, original contracts or
solution modules. The [independent specification guide](lean/ReyZygmund/MathlibOnly/README.md)
and [consistency checks](CONSISTENCY.md) explain the proved identities relating
these definitions to those used in the proofs.

The [comparison adapters](verification/comparator/CASES.json) are short Lean
theorems connecting the library's results to the independently stated theorems.
[AUDIT-MANIFEST.json](verification/AUDIT-MANIFEST.json) records the exact
adapters, configurations, seven-result mapping and declaration/contract inventory.
The permitted axioms are the same three as in step 2.

Each `ChallengeN.lean` contains an intentional `sorry` placeholder for the
proof to be supplied by its solution. Isolated negative-test fixtures also
deliberately contain an admission or a custom axiom. These files are outside
the production source inventory, and solutions cannot import them.

Use a regular, unprivileged Linux user, working user-level systemd, and a
Landlock-capable kernel. On macOS, a Linux VM such as Lima supplies this
environment. Do not use `fake-landrun.sh` for these checks. The runner includes
a sandbox preflight, the upstream AF_UNIX restriction and bounded
resources (6 GiB memory, no swap, a 200% CPU quota, one hour per case).

Install the same Lean and dependency sources/cache **inside Linux**, then
follow [Linux checker setup](verification/LINUX-SETUP.md) for the four pinned
checker tools. The authoritative versions are in
[CHECKER-PINS.json](verification/CHECKER-PINS.json); do not substitute current
default branches.

The seven configurations correspond to the
[incomparable maximal estimate](verification/comparator/config-1.json),
[sparse incomparable overlap estimate](verification/comparator/config-2.json),
[maximal and overlap estimates under weaker containment](verification/comparator/config-3.json),
[rounded dyadic endpoint estimate](verification/comparator/config-4.json),
[continuous Zygmund endpoint estimate](verification/comparator/config-5.json),
[sparse Φ-Zygmund overlap estimate](verification/comparator/config-6.json), and
[sharpness for the classical dyadic Zygmund family](verification/comparator/config-7.json).

```sh
python3 -I -B tools/comparator.py
```

To test the runner first, execute `python3 -I -B tools/test_comparator_runtime.py`
in this Linux environment; this test additionally requires a C compiler with
static libc support. See [Testing the verification tools](#testing-the-verification-tools).

The runner first checks exact source, adapter and configuration identities. It
traverses the local imports of each challenge and solution: a challenge may
use only the two independent specification modules, while a solution must not
import any challenge placeholder. The imported dependency sources are checked
against their pins. These checks establish the source boundary, not the
mathematical faithfulness of the definitions.

For an offline packet and import-boundary check without invoking Linux tools:

```sh
python3 -I -B tools/comparator.py --prepare-only
```

Its status is `PREPARED_NOT_CHECKED`, never proof acceptance.

The full runner creates a fresh packet, copies the dependency tree, and checks all
seven pairs sequentially. Acceptance requires a successful Comparator exit and
three explicit reports: successful comparison, Lean default-kernel acceptance
and Nanoda acceptance. The runner records those observations separately, checks
inputs and tool hashes at the end, and retains reports and complete logs under
`.runs/`. Only
`PASS_ALL_SEVEN` means the complete suite passed. `--case 7` is an optional
single-result smoke test and can produce only `PASS_ONE_CASE_ONLY`.

Both kernels checked the seven exported proofs and all declarations on which
those proofs depend. Other supporting results have the ordinary Lean checks
described above. In particular, `Continuous.Convention`,
`Continuous.HalfOpenBoundary`, `MathlibOnly.BoundaryBridge` (all under
`ReyZygmund`), `Verification.Inspect` and `Verification.Statements.MathlibOnly`
are outside those seven exports; their presence in the distribution does not
imply Nanoda coverage.

The Mathlib-only seven-result run used an 8 GiB ARM64 Linux VM,
completed in about 15 minutes with warm dependency caches, and had a measured
peak of about 4.5 GiB.
Allow at least 15 GiB free guest disk for the runner, in addition to installed
tools and dependencies. Other architectures or colder caches may cost more.

## What remains trusted

Separate mathematical reviews compared the formal statements and definitions
with the paper, and checked the proofs relating the independent statements to
the library. This correspondence requires mathematical judgment: Comparator
compares formal statements, not the paper's text. Lean and Nanoda check the
resulting proof terms. The permitted axioms, dependency sources and caches,
toolchain and operating environment are explicit parts of the setup. The checks
cover the seven proofs and the definitions and results they depend on, rather
than every result in the imported libraries.

The guide follows the pinned [Comparator documentation](https://github.com/leanprover/comparator/blob/d03acab154d269c06e60e4de7e4cc85deebff94b/README.md).

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

`test_comparator_runtime.py` runs a tiny Linux comparison with both kernels,
then repeats it with a missing Nanoda binary and a deliberately failing static
test binary. Both failures must be rejected by the same acceptance function as
the production runner. It also tests rejection of a changed definition and an
indirect admission. The test requires a C compiler with static libc support;
it never replaces the installed Nanoda or edits the seven production configs.

All fixture scripts retain reports with status `PASS_FIXTURES_ONLY`, distinct
from production acceptance. Scratch copies are left under `.runs/` for inspection.
