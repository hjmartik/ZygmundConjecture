# Independently inspectable mathematical statements

This independent specification is rebuilt from Mathlib primitives.
The six propositions in [Statements.lean](Statements.lean)
use only Mathlib and the definitions in [Definitions.lean](Definitions.lean).
Neither file imports the proof library. The statements and all definitions
needed to interpret them can therefore be inspected without reading that library.

The results concern Henri Martikainen's *The Zygmund conjecture and Rey's
exponential integrability conjecture*. The central statements are the
weakly incomparable maximal estimate, the sparse weakly incomparable overlap
estimate, and the continuous Zygmund endpoint. The overlap estimate proves
Rey's conjecture. The rounded endpoint supports the continuous result; the
other two statements concern overlap for sparse Φ-Zygmund families and
sharpness for the classical dyadic Zygmund family.

| Mathematical statement | Proposition in `Statements.lean` | Proof of the independent statement |
| --- | --- | --- |
| Weakly incomparable maximal estimate | [WeaklyIncomparableMaximal](Statements.lean#L33) | [weakly_incomparable_maximal](Solutions.lean#L19) |
| Sparse weakly incomparable overlap estimate | [WeaklyIncomparableOverlap](Statements.lean#L47) | [weakly_incomparable_overlap](Solutions.lean#L31) |
| Continuous Zygmund endpoint | [ContinuousEndpoint](Statements.lean#L64) | [continuous_endpoint](Solutions.lean#L49) |
| Rounded dyadic endpoint | [RoundedEndpoint](Statements.lean#L78) | [rounded_endpoint](Solutions.lean#L59) |
| Sparse Φ-Zygmund overlap | [PhiSparseOverlap](Statements.lean#L92) | [phi_sparse_overlap](Solutions.lean#L69) |
| Sharpness for the classical dyadic Zygmund family | [PhiSparseSharpness](Statements.lean#L109) | [phi_sparse_sharpness](Solutions.lean#L88) |

The propositions and their proofs are in the namespace `ReyZygmund.MathlibOnly`.
[Solutions.lean](Solutions.lean) derives the six statements from the proof
library's theorems. The [consistency guide](../../../CONSISTENCY.md) explains
the connections between the specification's definitions and those used in the proofs.

The maximal statement uses the paper's `1 < p ≤ 2` range. The
[underlying theorem](../Maximal/WeakerGlobal.lean#L140) proves the same weakly
incomparable estimate for every real `p > 1`.

The maximal function and overlap take values in `[0, ∞]`.
The maximal and overlap bounds use these quantities directly.

The sharpness result concerns the
[classical dyadic Zygmund family](../../../MAIN-STATEMENTS.md#sharpness-for-the-classical-dyadic-zygmund-family).
Here `n = m - 1`, where `m` is the number of cube factors.
For `n ≥ 2`, `0 < eta < 1` and any choice of dyadic grids in the `n + 1` cube
factors, it gives a sequence of finite incomparable `eta`-sparse families `G_N`,
`N ≥ 2`, whose unions have measure one.
For every `c > 0` and `beta > 1/n`, the integrals of `exp(c h^beta)` over
these unions tend to infinity, where `h` is the overlap function of the
corresponding family. The same sequence works for all such `c` and `beta`.

## Definition reference

The mathematical objects used in the six statements are defined in
[Definitions.lean](Definitions.lean):

| Definition | Mathematical meaning |
| --- | --- |
| [Point](Definitions.lean#L36), [Rectangle](Definitions.lean#L40) | Euclidean points and tuples of box factors |
| [CubeGrid](Definitions.lean#L44) | Dyadic cube grids with side length `2 ^ k` at scale `k`, partitions at each scale and nesting |
| [rectangle](Definitions.lean#L60) | Products of box factors, expressed by Euclidean coordinate inequalities using `(lower, upper]` |
| [gridRectangles](Definitions.lean#L66) | All products of cubes from the given grids |
| [shadow](Definitions.lean#L73), [overlap](Definitions.lean#L79) | Union of the rectangles and the number containing each point, allowing infinity |
| [Sparse](Definitions.lean#L98) | Pairwise disjoint Lebesgue-measurable subsets of the rectangles with the required volume fraction |
| [Incomparable](Definitions.lean#L84) | No two distinct rectangles contain one another |
| [WeaklyIncomparable](Definitions.lean#L90) | No strict containment in every cube factor |
| [maximal](Definitions.lean#L107) | Supremum of averages of the absolute value of the function over rectangles containing the point |
| [rectangleIco](Definitions.lean#L153), [maximalIco](Definitions.lean#L160) | Rectangles using `[lower, upper)` in each scalar coordinate and their maximal function |
| [continuousRectangles](Definitions.lean#L116) | Rectangles at all positions with arbitrary positive first side lengths and the last prescribed by `phi` |
| [rounding](Definitions.lean#L124), [roundedScales](Definitions.lean#L128) | The ceiling rule for rounding side lengths and every resulting tuple of scales |
| [shiftedCubes](Definitions.lean#L137), [roundedRectangles](Definitions.lean#L146) | The explicitly defined shifted grids and their rounded rectangle families |
| [phiRectangles](Definitions.lean#L169) | Dyadic rectangles whose last side-length exponent is prescribed by `Phi` from the other exponents |
| [exp](Definitions.lean#L176) | The exponential on `[0, ∞]`, with `exp ∞ = ∞` |

Boxes, finite coordinate products, Lebesgue measure, integrals, extended
nonnegative numbers, powers and norms use Mathlib's definitions directly.
The Lean source comments explain the notation used in these definitions and
statements.

A box `Q` has corner tuples `Q.lower` and `Q.upper`; the expression
`(Q : Set (Fin d → ℝ))` denotes the product of the intervals
`(Q.lower j, Q.upper j]`. In the sharpness statement,
`Tendsto (fun N => a N) atTop atTop` means `a N → +∞` as `N → ∞`.

## Verification and mathematical review

Mathematical review assesses whether the statements and their definitions
faithfully represent the paper's results. Comparator checks that the supplied
theorems match the independent specification, including its definitions.
Lean's default kernel, Nanoda and con-ron check the exported proofs and their
exported dependencies. The [verification guide](../../../VERIFYING.md) records
the checks, their scope and reproduction instructions.
