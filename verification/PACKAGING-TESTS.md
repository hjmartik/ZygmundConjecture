# Tests of the verification tools

The tests below check that the verification tools recognize valid proofs,
reject invalid inputs, and recover missing compiled dependencies. They use the
pinned Lean 4.34.0 toolchain. The scope of the mathematical verification is
described in [the verification guide](../VERIFYING.md).

## Checks after wording changes, 26 September 2026

The public mathematical guides and source comments were edited for clarity.
Comparison with the checked sources confirmed that all code outside comments
and all source line numbers are unchanged across the 363 modules. Source
hashes and generated pages were refreshed. The 453 declaration/contract
mappings, fourteen comparison adapters, seven configurations, dependency
pins and public checking programs are unchanged.

Thirteen lightweight wrapper tests and offline comparison-packet preparation
passed after the wording changes. The Lean builds, replay, compiled inspection
tests, Comparator and Nanoda runs described below preceded these editorial changes.

## Checking the Mathlib-only statements, 26 September 2026

The independent statements and proofs relating them to the main development
add 14 local modules and 15 registered declarations to the original 349 modules
and 438 contracts. The combined inventory is 363 modules and 453 declarations,
covering the same seven main results. The comparison runner uses the reviewed
Mathlib-only Challenge/Solution pairs and configurations.

The following focused tests passed:

- Thirteen wrapper test methods on macOS and Linux, including exact source
  and adapter binding, the rounded/continuous target order, missing new
  modules, transitive proof-library imports into challenges and challenge
  placeholders imported by solutions.
- Seven compiled Lean-inspection fixtures on macOS, with the same production
  inspector and acceptance code. Wrong-origin and definitional-equality
  boundaries are included.
- Five Linux runtime fixtures with the pinned Comparator, Lean and
  Nanoda: valid acceptance, missing Nanoda, failing Nanoda, a changed
  referenced definition and an indirect admission. The missing/failing
  Nanoda cases explicitly observed Lean acceptance but rejected overall
  acceptance.
- Offline production packet construction and its fourteen local import
  closures. Each challenge contains only itself and the two independent
  specification modules; solutions do not import challenge placeholders.

The combined public build/inspection also passed: all **363 modules** compiled
fresh on macOS and all **453 registered declarations** matched their reviewed
contracts and permitted transitive axioms. The public Linux runner completed
all **seven Mathlib-only comparisons**, with successful exits and explicit
Comparator, Lean default-kernel and Nanoda acceptance for every case. The
seven cases took about 14 minutes in total with warm dependency caches.

These runs used the distributed checking programs. Their source files,
comparison inputs and logs were checked for consistency after completion.
Dependency recovery had already passed the tests described below. Ordinary
kernel replay had already completed for both the original library and the
added layer. Those checks were not repeated in this run. The recovery
implementation and all dependency and checker pins were unchanged.

## Invalid-input rejection, 25 September 2026

On 25 September 2026, the following local tests passed:

- Ten wrapper test methods, including persistent regressions for changed or
  missing mathematical sources and missing or duplicate registered targets.
- Seven Lean inspector fixture cases. In particular, a reducible
  definitionally equal presentation passed, while a merely logically
  equivalent presentation and a declaration from the wrong source module were
  rejected. The prior indirect-admission, custom-axiom and changed-statement
  boundaries remained covered.
- Comment-stripped dependency-header parsing correctly distinguished a
  `module` command from that word occurring only in a comment.

On 25 September 2026, five isolated fixtures also passed in the Linux ARM64
checker environment with the pinned Comparator, Lean, Nanoda and Landrun:

| Fixture | Required and observed behavior |
| --- | --- |
| Valid proof | Comparator, Lean and Nanoda all accepted. |
| Nanoda absent | Lean accepted, but overall acceptance failed. |
| Nanoda deliberately failing | Lean accepted, but overall acceptance failed. |
| Changed referenced definition | Comparator rejected the mismatch. |
| Indirect admission | The exported proof dependency on `sorryAx` was rejected. |

The runner retained complete logs and separate kernel outcomes. These tests
use small fixture theorems, rather than the seven main results.

## Dependency recovery, 25 September 2026

The recovery completeness check requires the full set of compiled files used by
the pinned direct compiler: `.olean`, `.olean.server`, `.olean.private`,
`.ir.sig` and `.ir` for split modules. The same check runs before reuse, after
compilation and after installation.

On 25 September 2026, all three isolated recovery cases passed on macOS ARM64:

| Deliberately absent from the scratch cache | Observed result |
| --- | --- |
| All compiled files for `Mathlib.Analysis.SpecialFunctions.Log.Base` | Import failed; source recovery rebuilt the module; compilation and production contract/axiom inspection then passed. |
| Only `.olean.server` | The retained `.olean` and `.olean.private` did not mask the omission. Import failed on the server file; recovery rebuilt the module and inspection passed. |
| Only `.ir`, with `.ir.sig` retained | Import failed on the IR file; recovery rebuilt the module and inspection passed. |

Each case rebuilt only the selected module, preserved the source pins and
original cache, and checked backups of retained scratch files that were
replaced. Eight wrapper unit tests passed, including a new test for each member
of the required set of compiled files. These tests concern dependency setup;
they do not repeat mathematical verification. The Linux runtime tests had
already passed in the earlier run below and were not repeated as part of
these recovery tests.

## Earlier test coverage

| Test | Observed result |
| --- | --- |
| Lean inspection fixtures, macOS ARM64 | A valid theorem passed. An imported indirect admission, a custom axiom, a changed conclusion and an extra assumption were rejected. All five use the production Lean inspector and Python acceptance function. |
| Offline dependency recovery, macOS ARM64 | The compiled files for `Mathlib.Analysis.SpecialFunctions.Log.Base` were omitted from an isolated cache view. A test theorem failed to import it, recovery rebuilt it from the existing pinned source, and the theorem then compiled and passed production contract/axiom inspection. Source pins and the original cache were unchanged. |
| Comparator/Nanoda fixtures, Linux ARM64 | A tiny valid theorem passed Comparator, Lean and Nanoda. With Nanoda absent, or replaced **only within the fixture** by a deliberately failing executable, Lean still accepted but the run failed overall. All three use the production resource wrapper, child invocation and acceptance function. The sandbox preflight also passed. |
| Wrapper unit tests | Seven test methods passed, covering inventory, report acceptance/rejection, missing/duplicate reports, archive safety, dependency-header parsing and required-kernel acceptance. |
| Production packet construction | All seven original Challenge/Solution pairs and configurations were prepared without running the seven-result suite again. |

Fixture sources are in `verification/fixtures/`, outside the production
inventory (349 modules in these earlier tests; 363 after adding the Mathlib-only statements).
Negative fixtures deliberately contain invalid
verification inputs; they are never imported into production proofs. Test
harnesses do not reduce the registered declaration list, change the seven main
contracts, or enlarge the allowed axiom set. Success is labeled
`PASS_FIXTURES_ONLY`, not proof acceptance.

## Repeating the tests

From the repository root:

```sh
python3 -I -B tools/test_checker.py
python3 -I -B tools/test_inspection.py
python3 -I -B tools/test_recovery.py --packages lean/.lake/packages
```

The recovery test needs existing pinned sources and a compatible populated
dependency cache. It creates three fresh scratch views. Retained artifacts of
the selected module are copied, not symlinked, so recovery can replace them
without touching the original cache. Other cached objects are linked for
read-only use. Each case rebuilds the selected module's complete artifact
family. It neither downloads anything nor removes files from the original cache.

After the [Linux checker setup](LINUX-SETUP.md), run in Linux:

```sh
python3 -I -B tools/test_comparator_runtime.py
```

This requires the real pinned Nanoda installation and a C compiler with static
libc support; the missing/failing variants are controlled fault injections,
not alternate production checker options. The script retains complete logs
and separate kernel outcomes. The installed checker binaries remain unchanged.
Use `--lean-bin` with any fixture script that invokes Lean to select the exact
installed compiler explicitly; the Linux script also accepts `--tools`.

Reports and scratch directories are retained under `.runs/`. The repository
does not include machine-specific logs. `PUBLIC-FILES.sha256` identifies the distributed
scripts and fixtures. A failed or interrupted fixture run is not a passing test.

## Earlier export checks and limitations

The earlier public-export test freshly checked all 349 local modules and
438 registered declarations and ran the seventh main result through the public
Linux Comparator/Nanoda runner. Those checks, and the original all-seven
dual-kernel checks and ordinary replay, are historical evidence. The current
Mathlib-only integration tests are listed separately above. The original
mathematical code and contracts remain unchanged; the later editorial revision
changes only source comments. The added layer and comparison adapters were
checked against the source files recorded for those runs.

The recovery test exercised one Mathlib module used by this development, with existing
compatible dependency caches, not a complete Mathlib rebuild from an empty
cache. Fresh internet provisioning and other operating systems were not tested
in the recovery tests.
