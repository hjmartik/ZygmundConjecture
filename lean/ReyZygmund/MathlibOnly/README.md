# Independent statements of the seven main results

The results concern maximal functions and the overlap of rectangle families in
$\mathbb R^{d_1}\times\cdots\times\mathbb R^{d_m}$. They include the Zygmund
endpoint estimate, Rey's exponential integrability estimate, and the
incomparable maximal estimate used to prove them, together with the extensions
and sharpness result listed below.

Here the seven results are stated using independently written definitions of
the cubes, rectangles and operators. A reader can inspect these statements
without tracing definitions through the proofs. The
[definitions](Definitions.lean) and [statements](Statements.lean) use only
Mathlib and do not import the proof library or its earlier statements.
The mathematical formulations, with all hypotheses and constants, are in the
[Main theorems](../../../MAIN-STATEMENTS.md).

| Result | Lean proof of the independently stated result |
| --- | --- |
| Incomparable maximal estimate | [Proof](SolutionMaximal.lean) |
| Sparse incomparable overlap estimate | [Proof](SolutionOverlap.lean) |
| Maximal and overlap estimates under weaker containment | [Proof](SolutionWeaker.lean) |
| Rounded dyadic endpoint estimate | [Proof](SolutionRounded.lean) |
| Continuous Zygmund endpoint estimate | [Proof](SolutionContinuous.lean) |
| Sparse Φ-Zygmund overlap estimate | [Proof](SolutionPhiSparse.lean) |
| Sharpness for the classical dyadic Zygmund family | [Proof](SolutionSharpness.lean) |

## The mathematical definitions

Dyadic cubes have side length $2^k$ at scale $k$, partition the space at each
scale, and are nested whenever they intersect. Dyadic rectangles are products of these
cubes. The definitions of sparseness, incomparability and the weaker containment
condition use the usual subsets and inclusions. The shadow of a family is its
union, its overlap is the sum of its indicators, and its maximal function takes
the supremum of averages of $|f|$ over rectangles containing a point.

The continuous family allows arbitrary locations and all positive values of
the first $m-1$ side lengths, with the last side prescribed by $\phi$.
For the dyadic covering argument, every tuple obtained by rounding these side
lengths is retained: the first $m-1$ rounded scales need not determine the last
one. The dyadic $\Phi$-Zygmund family is specified directly by its side-length
relation.

These definitions are given in [Definitions.lean](Definitions.lean).
The [consistency guide](../../../CONSISTENCY.md) explains their mathematical
meaning, including the Borel sets used for sparseness, the half-open cube
conventions and the use of possibly infinite nonnegative sums and integrals.

## Relating the statements to the proofs

The two descriptions of a dyadic grid are proved equivalent for every grid.
The cubes are unchanged; the side-length exponent $k$ corresponds to generation
$n=-k$ in the proofs. In particular, the usual dyadic children follow from the
independent grid definition, and the constructed shifted grids satisfy it.
See the [grid equivalence](GridBridge.lean) and
[shifted grids](../Geometry/ShiftedGrid.lean).

The corresponding rectangles, families and operators are then proved equal.
This includes all the rectangles in the continuous and rounded families.
For locally integrable functions, the nonnegative-integral formula for an
average agrees with the real-integral formula used in the proofs.
See the [identities for rectangles and operators](OperatorBridge.lean),
[equalities of dyadic families](FamilyBridge.lean), and
[boundary conventions and measurability](BoundaryBridge.lean).

The seven theorems follow from the existing results through these identities.
Their hypotheses and conclusions were independently reviewed against the paper.
Comparator then checked the seven independently stated results, and Lean and
Nanoda accepted their proofs. This comparison supplements mathematical review;
it does not replace the judgment needed to translate a paper into formal
statements. The [verification guide](../../../VERIFYING.md) gives the checking
scope and instructions for repeating the checks.
