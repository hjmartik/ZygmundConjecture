# Tests of the checking programs

These tests check that the verification programs accept valid inputs, reject
deliberately invalid ones and recover missing compiled dependencies.
The mathematical verification results are recorded separately in
[RESULTS.json](RESULTS.json).

Test outcomes and checking-program identities are recorded in
[TOOLING-RESULTS.json](TOOLING-RESULTS.json). The eight Linux runtime fixtures
passed in the freshly provisioned VM used for the six-result checks.

## Lightweight tests

The 13 tests in `tools/test_checker.py` passed, covering inventories, changed
or missing sources, duplicate targets, origins, import separation, configuration
identities, axiom restrictions, archive safety and artifact completeness.

The 13 tests in `tools/test_comparator_acceptance.py` passed, covering the four
required acceptance reports, failed exits, configuration, environment and
sandbox command construction. Timeout cleanup uses a mocked process; these
tests do not themselves execute a sandbox or kernel.

These tests require only Python 3.12 or later and the repository.

```sh
python3 -I -B tools/test_checker.py
python3 -I -B tools/test_comparator_acceptance.py
```

## Compiled Lean inspection

The [statement-and-axiom checking program](../lean/Verification/Inspect.lean),
written in Lean, compares each registered theorem with a separately written
expected statement, called its contract. It checks definitional equality with
full unfolding transparency: definitions may be unfolded, but merely logically
equivalent statements do not count as matching. The expected statements are
listed in [TARGETS.json](TARGETS.json). The surrounding Python checks reject
missing or duplicate reports, wrong declaration origins and unapproved axioms,
including indirect uses of an omitted proof. The fresh-build command also
rejects compiler warnings and changed source files.

Seven Lean inspection fixtures passed their expected outcomes. A valid theorem
and a definitionally equal presentation were accepted. A merely logically
equivalent presentation, indirect admission, custom axiom, changed conclusion
and extra assumption were rejected. The valid case also tested wrong-origin
rejection through the [statement-and-axiom checking program](../lean/Verification/Inspect.lean)
and its report checks.

```sh
python3 -I -B tools/test_inspection.py
```

## Linux comparisons

Eight Linux fixtures passed their expected outcomes with the pinned tools:

| Fixture | Observed outcome |
| --- | --- |
| Valid theorem | Comparator, Lean, Nanoda and con-ron accepted. |
| Extra assumption | Rejected for the statement mismatch. |
| Changed definition | Rejected for the mismatch. |
| Indirect admission | Rejected for `sorryAx`. |
| Missing Nanoda | Rejected for the missing executable. |
| Failing Nanoda | The regular executable ran and printed its marker; Lean and con-ron accepted, Comparator rejected. |
| Missing con-ron | Rejected for the missing executable. |
| Failing con-ron | The regular executable ran and printed its marker; Lean and Nanoda accepted, Comparator rejected. |

The deliberately failing executables exit 73. The public record includes their
hashes, invocation markers and log hashes; the full logs remain in the test run
directories. The runtime preflight tested network
namespace isolation, denied writes outside the checking directory and permitted
scratch writes. The checking process confirmed its memory and swap limits.

```sh
python3 -I -B tools/test_comparator_runtime.py
```

## Native macOS comparisons

The optional local runner was tested on an Apple Silicon Mac with the pinned
Lean toolchain. Its nine small cases cover a valid theorem, an extra assumption,
a changed definition, an indirect admission, a custom axiom, and missing or
deliberately failing Nanoda and con-ron executables. Each produced its intended
outcome. Both failing executables ran and printed their markers; Lean and the
other checker accepted while Comparator rejected.

Three additional checks covered the required trust acknowledgement, selection
of the local toolchain without inherited checker overrides, and an actual
timeout. The test receipt is recorded under `native_macos_fixtures` in
[TOOLING-RESULTS.json](TOOLING-RESULTS.json).

```sh
python3 -I -B tools/test_comparator_local.py --trust-project-code
```

These tests deliberately run **without a sandbox** and do not establish sandbox
protection. Their success label is `PASS_LOCAL_FIXTURES_ONLY`. The existing
sandboxed Linux procedure and its test results are unchanged.

The complete local command was also exercised on all six main results using
the existing matching Mathlib cache. All six comparisons and all three proof
checkers succeeded, with status `PASS_ALL_SIX_UNSANDBOXED`. This validates the
native Mac procedure; the recorded sandboxed verification remains the one
described in [the verification guide](../VERIFYING.md#what-has-been-checked).

## Dependency recovery

The three dependency-recovery fixtures passed with the pinned Linux tools:
a wholly absent compiled module, a missing `.olean.server`, and a
missing `.ir` with the other artifacts retained. Each detected the intended
import failure, rebuilt the module from pinned sources, and checked a small
theorem through the same statement-and-axiom checker. The original cache was unchanged.

```sh
python3 -I -B tools/test_recovery.py --packages lean/.lake/packages
```

## Source and packet checks

Source checks matched all 396 supplied Lean files exactly outside comments to the checked
code, the seven adapter files and six comparison configurations to the
checked inputs, and the 508 declaration mappings to their contracts. The selected
local build/replay closure contains 382 modules. Packet preparation passed its
source and import-boundary checks; preparation does not verify proofs.

See [the verification guide](../VERIFYING.md) for the mathematical checking scope and
reproduction instructions.
