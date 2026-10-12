# Tests of the checking programs

These tests check that the verification programs accept valid inputs, reject
deliberately invalid ones and recover missing compiled dependencies.
The mathematical verification results are recorded separately in
[RESULTS.json](RESULTS.json).

Test outcomes and checking-program identities are recorded in
[TOOLING-RESULTS.json](TOOLING-RESULTS.json). The Linux runtime and dependency-recovery
results are retained from earlier runs. The same record explains why those
results apply to the distributed files.

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

Seven Lean inspection fixtures passed their expected outcomes. A valid theorem
and a definitionally equal presentation were accepted. A merely logically
equivalent presentation, indirect admission, custom axiom, changed conclusion
and extra assumption were rejected. The valid case also tested wrong-origin
rejection through the production inspector and report checking.

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

## Dependency recovery

The three dependency-recovery fixtures also passed in the pinned Linux
environment: a wholly absent compiled module, a missing `.olean.server`, and a
missing `.ir` with the other artifacts retained. Each detected the intended
import failure, rebuilt the module from pinned sources, and checked a small
theorem through the production inspector. The original cache was unchanged.

```sh
python3 -I -B tools/test_recovery.py --packages lean/.lake/packages
```

## Source and packet checks

Source checks matched all 391 supplied Lean files to the checked code outside
comments, the seven adapter files and six comparison configurations to the
checked inputs, and the 497 declaration mappings to their contracts. The selected
local build/replay closure contains 377 modules. Packet preparation passed its
source and import-boundary checks; preparation does not verify proofs.

See [the verification guide](../VERIFYING.md) for the mathematical checking scope and
reproduction instructions.
