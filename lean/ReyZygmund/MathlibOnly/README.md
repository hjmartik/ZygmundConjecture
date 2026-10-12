# Independently inspectable mathematical statements

This independent specification is rebuilt from Mathlib primitives.
The six propositions in [SubmittedStatements.lean](SubmittedStatements.lean)
use only Mathlib and the definitions in [Definitions.lean](Definitions.lean)
and [SubmittedDefinitions.lean](SubmittedDefinitions.lean).
None of these files imports the proof library. The statements and all definitions
needed to interpret them can therefore be inspected without reading that library.

The results concern Henri Martikainen's *The Zygmund conjecture and Rey's
exponential integrability conjecture*. The central statements are the
weakly incomparable maximal estimate, Rey's overlap estimate, and the continuous
Zygmund endpoint. The rounded endpoint supports the continuous result; the other two statements
concern overlap for sparse Φ-Zygmund families and sharpness for the classical
dyadic Zygmund family.

| Mathematical statement | Proposition in `SubmittedStatements.lean` | Proof of the independent statement |
| --- | --- | --- |
| Weakly incomparable maximal estimate | [WeaklyIncomparableMaximal](SubmittedStatements.lean#L26) | [weakly_incomparable_maximal](SubmittedSolutions.lean#L37) |
| Sparse weakly incomparable overlap estimate | [WeaklyIncomparableOverlap](SubmittedStatements.lean#L40) | [weakly_incomparable_overlap](SubmittedSolutions.lean#L50) |
| Continuous Zygmund endpoint | [ContinuousEndpoint](SubmittedStatements.lean#L57) | [continuous_endpoint](SubmittedSolutions.lean#L94) |
| Rounded dyadic endpoint | [RoundedEndpoint](SubmittedStatements.lean#L70) | [rounded_endpoint](SubmittedSolutions.lean#L97) |
| Sparse Φ-Zygmund overlap | [PhiSparseOverlap](SubmittedStatements.lean#L83) | [phi_sparse_overlap](SubmittedSolutions.lean#L105) |
| Sharpness for the classical dyadic Zygmund family | [PhiSparseSharpness](SubmittedStatements.lean#L97) | [phi_sparse_sharpness](SubmittedSolutions.lean#L116) |

The propositions and their proofs are in the namespace
`ReyZygmund.MathlibOnly.Submitted`. [SubmittedSolutions.lean](SubmittedSolutions.lean)
proves the six statements using the proof library and the connections described
below.

The maximal statement uses the paper's `1 < p ≤ 2` range. The
[underlying theorem](../Maximal/WeakerGlobal.lean#L140) proves the same weakly
incomparable estimate for every real `p > 1`.

The maximal function and overlap are defined using nonnegative extended real
values, which may be infinite. The `L^p` maximal and sparse overlap statements
also assert that these quantities are finite almost everywhere under their
hypotheses. The real-valued functions used in the norms and exponential
integrals therefore agree with them outside a set of measure zero.

For the [classical dyadic Zygmund family](../../../MAIN-STATEMENTS.md#sharpness-for-the-classical-dyadic-zygmund-family),
the sharpness statement retains a stronger quantified form of the paper's remark.
For `m ≥ 3`, `0 < eta < 1` and every choice of dyadic grids, it gives a sequence
of finite incomparable `eta`-sparse families `G_N`, `N ≥ 2`, whose unions have
measure one.
For every `c > 0` and `beta > 1/(m-1)`, the integrals of `exp(c h^beta)` over
these unions tend to infinity, where `h` is the overlap function of the
corresponding family. The same sequence works for all such `c` and `beta`.

## Connections to the proof library

The independent grid definition uses cubes of side length `2^k` which partition
the whole space at each integer scale `k`, with intersecting cubes nested.
The proof library uses the usual dyadic children obtained by halving each side.
[GridBridge.lean](GridBridge.lean) proves that the two grid descriptions are
equivalent for arbitrary grids, keeping the cubes unchanged and relating the
scale indices by `n = -k`. Through this equivalence, the constructed
[shifted grids](../Geometry/ShiftedGrid.lean) also give examples of the independent
grid definition.

Weak incomparability rules out strict containment in every cube factor.
[SubmittedBridges.lean](SubmittedBridges.lean#L37) proves that this is equivalent
to the condition used in the proof library: when one rectangle contains another,
at least one cube factor is unchanged (`HasEqualFactorOnContainment`).

The independent sparsity definition allows Lebesgue-measurable subsets of the
rectangles. Here `NullMeasurableSet` expresses measurability for completed
Lebesgue measure. The proof library uses Borel subsets.
[SubmittedMeasure.lean](SubmittedMeasure.lean) proves that each of the subsets
in the sparsity definition can be replaced by a Borel subset of the same measure,
preserving containment, pairwise disjointness and the exact sparsity parameter.

The independent maximal operator is the supremum of averages of `|f|`, defined
using nonnegative integrals that may be infinite. For locally integrable `f`,
[OperatorBridge.lean](OperatorBridge.lean) proves that these averages agree with
the ordinary real-valued averages used in the proofs, and hence define the same
maximal function. The hypotheses of the maximal estimates supply the required
integrability on each rectangle.

The same file identifies the explicitly defined shifted cubes and rounded
families with those used in the proofs. Different original side lengths can
give the same first `m-1` rounded scales but different last scales; all these
tuples are retained. [FamilyBridge.lean](FamilyBridge.lean) proves that the two
grid descriptions give the same families of dyadic rectangles and the same
families satisfying the prescribed relations between side lengths.

Mathlib's boxes use `(a,b]` in each scalar coordinate, while the paper's shifted
grids use `[a,b)`. For locally integrable `f`,
[BoundaryBridge.lean](BoundaryBridge.lean) proves that the continuous maximal
functions for the two conventions agree at every point, using continuity of
the rectangle integrals under translation. For the countable rounded family,
the maximal functions agree almost everywhere. The same file proves that the
continuous maximal function is measurable.
The rounded statement uses `[a,b)` directly;
[SubmittedMeasure.lean](SubmittedMeasure.lean) proves that changing the convention
preserves the measures of its maximal-function level sets.

Some intermediate estimates are written for the exponential minus one.
[SubmittedBridges.lean](SubmittedBridges.lean#L52) converts these to the
exponential bounds in the statements by adding the measure of the shadow.

For each finite family in the sharpness construction,
[SubmittedMeasure.lean](SubmittedMeasure.lean) proves that the exponential is
integrable and that its nonnegative and ordinary real integrals agree.
The sharpness statement uses the real integrals: each is finite, and these
finite values tend to infinity along the sequence for the coefficients and
powers specified in the statement.

## Definition reference

Every project definition determining the six statements is in the three
specification files:

| Definition | Mathematical meaning and related proofs |
| --- | --- |
| `CubeGrid` | Dyadic cube grids with fixed side lengths, partitions at each scale and nesting; equivalence with the proof-library definition in [GridBridge](GridBridge.lean) |
| `rectangle` | Products of cube factors, expressed by Euclidean coordinate inequalities; `rectangle_eq_flat` |
| `gridRectangles` | All products of cubes from the given grids; `gridRectangles_eq` |
| `shadow`, `overlap` | Union of the rectangles and the number containing each point, allowing infinity; identities in [SubmittedMeasure](SubmittedMeasure.lean) |
| `Submitted.Sparse` | Pairwise disjoint Lebesgue-measurable subsets with the required volume fraction; `sparse_iff_borel` |
| `Incomparable` | No two distinct rectangles contain one another |
| `Submitted.WeaklyIncomparable` | No strict containment in every cube factor; [weaklyIncomparable_iff_equalFactor](SubmittedBridges.lean#L37) |
| `maximal` | Supremum of averages of `\|f\|` over rectangles containing the point; `maximal_eq_endpoint` |
| `rectangleIco`, `maximalIco` | Rectangles using `[a,b)` in each scalar coordinate and their maximal function; `rectangleIco_eq`, `maximalIco_eq` |
| `continuousRectangles` | Rectangles at all positions with arbitrary positive first side lengths and the last prescribed by `phi`; `continuousRectangles_eq` |
| `rounding`, `roundedScales` | The ceiling rule for rounding side lengths and every resulting tuple of scales; `rounding_eq`, `roundedScales_eq` |
| `shiftedCubes`, `roundedRectangles` | The explicitly defined shifted grids and their rounded rectangle families; `shiftedCubes_eq`, `roundedRectangles_eq` |
| `phiRectangles` | Dyadic rectangles whose last side-length exponent is prescribed by `Phi` from the other exponents; `phiRectangles_eq` |
| The six propositions listed above | Independent statements of the main results, with proofs in [SubmittedSolutions](SubmittedSolutions.lean) |

Boxes, finite coordinate products, Lebesgue measure, integrals, extended
nonnegative numbers, powers and norms use Mathlib's definitions directly.

## Verification and mathematical review

The six statements and their definitions were independently reviewed against the
paper. Their proofs passed the recorded local Lean checks: compilation,
comparison of registered declarations with their separately written formal
statements, checks of the axioms used by the proofs and their dependencies, and
a further kernel check of the selected compiled modules.

All six independently stated main results passed Comparator comparison, and
their exported proofs and exported dependencies were accepted by Lean's default
kernel, Nanoda and con-ron. Supporting results outside those exports are covered
by the ordinary Lean checks described in the [verification guide](../../../VERIFYING.md);
their presence in the library does not imply separate Nanoda or con-ron verification.

Mathematical review assesses whether the specification expresses the intended
mathematics. Comparator checks that the supplied theorems match the independent
specification, including its definitions. Lean, Nanoda and con-ron check the
exported proofs and their exported dependencies.
