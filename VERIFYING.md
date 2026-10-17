# Checking the formalization

You can inspect the mathematics without installing software, or reproduce the
computer checks yourself:

- **Read the statements and definitions.** [Main theorems](MAIN-STATEMENTS.md)
  and [supporting statements](SUPPORTING-STATEMENTS.md) link each result to its
  independent Lean specification. The [definition guide](lean/ReyZygmund/MathlibOnly/DEFINITIONS.md)
  explains its mathematical objects and their Lean representations.
- **Check the twenty-two proofs against those statements.** We recommend
  [sandboxed Comparator on Linux](#recommended-sandboxed-checking-on-linux).
  [Local checking on a Mac](#local-checking-on-macos) is a more accessible
  alternative if you trust the repository's executable code.
- **Explore the proofs in Lean.** [Ordinary compilation](#ordinary-compilation)
  lets you work with the library in a Lean editor. It is not a prerequisite
  for either Comparator route.

## Mathematical scope

[Main theorems](MAIN-STATEMENTS.md) states the three main results, and
[supporting statements](SUPPORTING-STATEMENTS.md) states the nineteen selected
supporting results, with their hypotheses and qualifications. All twenty-two use
the same checking standard. A reader assessing one result needs its statement
and definitions; this does not require assessing every other statement.

<a id="what-has-been-checked"></a>

## Checking scope

| Check | Scope |
| --- | --- |
| Compilation | The 404 selected local modules. |
| Statement and axiom checks | The 516 registered declarations, their separately written formal statements and their axiom dependencies. |
| Ordinary Lean replay | The 404 selected modules, with the exclusions explained [below](#ordinary-kernel-replay). |
| Comparator, Lean, Nanoda and con-ron | Twenty-two comparisons against the independent specification, followed by checking the exported proofs and their exported dependencies with all three kernels. |

All the checks above passed. The twenty-two comparisons and three-kernel checks
ran in a freshly provisioned Linux VM, using trusted pinned tools and libraries,
without imported project build artifacts. Project compilation and proof export
ran inside Comparator's sandbox. The procedure follows the
[documentation for the Comparator version used here](https://github.com/leanprover/lean4/blob/c29b6dda4f7c20e3eeaa717c4e565663c5cfa364/src/lake/Lake/CLI/Help.lean#L403-L499).

The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.
Nanoda and con-ron check the twenty-two exported proofs and their dependencies,
not every other declaration in the library. The source inventory contains
409 Lean files; the selected build and replay cover 404 modules, excluding
negative-test fixtures and other files outside their imports.

[RESULTS.json](verification/RESULTS.json) records the outcomes, dates,
software versions and exact checked sources.
[Tests of the checking programs](verification/PACKAGING-TESTS.md) are recorded
separately.

## What the programs do

**Lean** is the language in which the statements and proofs are written. Its
kernel is the component that checks the fully explicit proofs produced when
the files are compiled.
**Mathlib** is the library of background mathematics used by this development.
**Lake**, supplied with Lean, manages the libraries and compilation.

**Comparator** checks that the supplied theorems match the independent
specification, including the definitions determining their meaning, and use
only the permitted axioms. It also submits the exported proofs to Lean's
kernel and, in our procedure, to **Nanoda** and **con-ron**, two additional
proof checkers. They check the proofs and the declarations those proofs depend on.

<a id="what-remains-trusted"></a>

Mathematical review compared the independent Mathlib-only statements and their
definitions with the paper. The formal checks verify the proofs of those
statements, including the identifications connecting the specification to the
proof library. Comparator does not compare Lean with the paper's prose: reading
the specification remains the way to assess whether it expresses the intended
mathematics.

Our Python programs prepare the inputs, invoke these tools and collect their
results. They do not replace the proof checkers. The setup commands obtain the
recorded software versions; no manual selection of library versions is needed.

<a id="recommended-verify-the-main-results"></a>
<a id="4-comparator-with-nanoda-on-linux"></a>
<a id="4-comparator-with-lean-nanoda-and-con-ron-on-linux"></a>

## Recommended: sandboxed checking on Linux

This is the strongest checking procedure supplied here for all twenty-two
results. Comparator runs the project code in a restricted environment, its
**sandbox**, to prevent that code from interfering with the checking process.
This reduces the trust you need to place in the proof library's executable code.

We recommend a **fresh Linux virtual machine**: a separate Linux environment
running on your computer, including on a Mac. A correctly configured Linux
computer can also run the sandboxed checks without a VM.

Preparing this environment takes more technical work than the local Mac route
below. Follow the [Linux setup and checking guide](verification/LINUX-SETUP.md)
**from start to finish**. Its four numbered steps cover preparing Linux and
the tools, obtaining the repository, preparing the libraries and testing the
setup, and checking all twenty-two results. It includes the final checking command
and explains how to read its result; you do not need to return here to complete
the procedure.

Run that procedure in a terminal **inside Linux**, including when Linux runs
in a VM on your Mac. Do not compile the project beforehand in that environment;
the guide runs its first compilation inside Comparator's sandbox.

<a id="1-install-the-pinned-dependencies"></a>

## Local checking on macOS

You can run the same comparisons and proof checkers directly on a Mac, without
setting up Linux. This route **disables Comparator's sandbox**. It remains
useful for checking the mathematics, but additionally trusts the project code
not to alter the specification or interfere with the checking tools. It does
not reproduce the sandbox guarantees of the recommended procedure.

You need Python 3.12 or later, Apple's command-line developer tools, and
[elan](https://github.com/leanprover/elan), which installs and selects Lean.
The developer tools provide Git and a C compiler. If you do not yet have a
local copy of the repository, obtain one:

```sh
git clone https://github.com/hjmartik/ZygmundConjecture.git
cd ZygmundConjecture
```

From the repository's top-level directory, run:

```sh
elan toolchain install leanprover/lean4:v4.35.0-rc4
python3 -I -B tools/dependencies.py fetch
python3 -I -B tools/dependencies.py cache
python3 -I -B tools/comparator_local.py --trust-project-code
```

The first three commands install Lean, download the background libraries and
obtain their compiled files, saving a lengthy library build. The last command
builds this project's proofs in a new working directory and checks all twenty-two
results. The local runner uses space-saving copies on APFS, the usual Mac disk
format. Allow at least 15 GiB of free space after installing the libraries.

The explicit `--trust-project-code` option acknowledges the additional trust
described above. Lake prints a warning that the sandbox is disabled; the
statement comparisons and proof checks still run. Successful completion is
reported as **`PASS_ALL_TWENTY_TWO_UNSANDBOXED`**, with separate results for Comparator
and all three kernels. The distinct label records the difference in setup.

## Optional: compile and check the Lean library

### Ordinary compilation

For interactive proof reading or experimentation, install Lean and the
background libraries using the first three local-setup commands above. Then:

```sh
cd lean
lake build
cd ..
```

This compiles the main-results entry point and its imports. These commands also
work on Linux with Python, Git, `curl`, a C compiler and elan installed. If you also
follow the clean-VM procedure, run this optional build in a different
environment, or wait until the sandboxed checks have finished.

<a id="2-build-and-check-all-registered-declarations"></a>

### Fresh build and statement checks

To check the registered library declarations, run from the top-level directory
after the same dependency setup:

```sh
python3 -I -B tools/test_checker.py
python3 -I -B tools/test_inspection.py
python3 -I -B tools/check.py verify
```

The first two commands test the checking programs. The third builds all 404
selected modules afresh and checks the statements and axiom dependencies of
the 516 registered declarations. Success requires a successful exit and `PASS`
in its report. The [checking-program guide](verification/PACKAGING-TESTS.md#compiled-lean-inspection)
explains precisely how statements are compared.

<a id="3-ordinary-kernel-replay"></a>

### Ordinary kernel replay

The fresh build already checks proofs with Lean’s kernel. This optional step
checks the saved proof terms again in a separate invocation, without rerunning
the tactics that constructed them.

Use the report path printed by the preceding command:

```sh
python3 -I -B tools/check.py replay --run .runs/VERIFY-RUN/report.json
```

Replace `VERIFY-RUN` with that run's directory name. Replay confirms that the
inputs and compiled files still match, then rechecks the selected modules.
It does not replay all of Mathlib, and the checker excludes unsafe and partial
constants.

<a id="understanding-the-setup"></a>

## Versions and setup details

The instructions use Lean **4.35.0-rc4** and fixed versions of Mathlib and its
supporting libraries. These are the **pinned versions**. Keep them when
reproducing these checks; do not replace the setup commands with `lake update`.
[SOURCE_LOCK.json](lean/SOURCE_LOCK.json) and
[CHECKER-PINS.json](verification/CHECKER-PINS.json) record them.

The **cache** is a download of already compiled background-library files. It
saves setup time; downloading it is not itself proof verification. **Hashes**
or **checksums** identify particular files. The scripts use them to detect
changed inputs; they are not a substitute for mathematical or proof checking.

## Troubleshooting dependency setup

If a required compiled dependency is missing, rebuild the missing files from
the already downloaded sources:

```sh
python3 -I -B tools/dependencies.py recover
```

After `PASS_DEPENDENCY_RECOVERY`, repeat the command that failed. Recovery works
offline and preserves the library versions. Compiled files are platform-specific:
do not transfer a Mac's build files into the Linux checking environment.

## Testing the verification tools

[Tests of the checking programs](verification/PACKAGING-TESTS.md) describes the
small valid and deliberately invalid examples and how to repeat them. Passing
those tests is not verification of the twenty-two mathematical results.

The [comparison cases](verification/comparator/CASES.json) identify the twenty-two
targets. Challenge files state the requested results with intentional proof
placeholders; the solutions supply the proofs without using those placeholders.
The [source inventory](verification/SOURCE-MANIFEST.json) and
[comparison inventory](verification/AUDIT-MANIFEST.json) identify the checked
files. `PUBLIC-FILES.sha256` lists checksums for the distributed files.
