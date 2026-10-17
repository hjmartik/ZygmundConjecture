# Mathematical objects and their Lean definitions

The specification uses cubes and rectangles, families of rectangles,
maximal and overlap functions, and dyadic averaging and difference operators.
This guide explains how these objects are represented in Lean and links to
their definitions. Where a useful identification requires a proof, that proof
is linked alongside the explanation.

The [specification guide](README.md) lists the statements and the definitions
needed for each result.

## Cubes, rectangles and coordinates

Mathlib's `Box` records the lower and upper corners of an axis-parallel box.
For `Q : Box (Fin d)`, these are the tuples `Q.lower` and `Q.upper`, with
strictly positive width in each coordinate. The expression
`(Q : Set (Fin d → ℝ))` denotes the product of the intervals
`(Q.lower j, Q.upper j]`.

A [Rectangle](Definitions.lean#L41) is a tuple of these boxes, one for each
coordinate block of dimension `d i`. The rectangle families below impose the
cube and side-length conditions on its factors. The function
[rectangle](Definitions.lean#L61) turns that tuple into a subset of
$`\mathbb R^d`$, where $`d=\sum_i d_i`$.

[CubeGrid](Definitions.lean#L45) describes a dyadic grid by its cubes at each
integer scale: cubes of side $`2^k`$ partition the space, and intersecting cubes
are nested. [gridRectangles](Definitions.lean#L80) consists of all products of
cubes from the supplied grids, with the scale chosen independently in each factor.

[Point](Definitions.lean#L37) lists all scalar coordinates in one tuple.
For operators acting in selected coordinates,
[ProductPoint](SquareFunctions.lean#L31) groups them into the blocks
$`\mathbb R^{d_1}\times\cdots\times\mathbb R^{d_m}`$;
[productRectangle](SquareFunctions.lean#L34) describes the same rectangle in
these grouped coordinates. The identification is
[measure preserving](../Geometry/Flatten.lean#L52), with the corresponding
[rectangle, integral and norm identities](../Geometry/FlatRectangles.lean)
proved in Lean.

[appendLastPoint](Definitions.lean#L69) appends the last coordinate block to the first
blocks, giving the point $`(x,t)`$ used in the slicing identities.

## Families of rectangles

A family is a set of rectangles, written `G : Set (Rectangle d)`.
[WeaklyIncomparable](Definitions.lean#L112) means that no two members are
strictly nested in every factor. Lean proves the
[equivalent formulation](Proof/IncomparabilityBridge.lean#L35): whenever one
member contains another, at least one factor is unchanged.
[Incomparable](Definitions.lean#L106) is the stronger condition that no two
distinct members contain one another.

[Sparse](Definitions.lean#L120) expresses sparseness through pairwise disjoint
sets $`E_R\subset R`$ with $`|E_R|\geq\eta|R|`$.
`NullMeasurableSet` means that these sets are measurable for completed
Lebesgue measure.

[zygmundRectangles](Definitions.lean#L139) specifies the continuous family:
all positions are allowed, the first side lengths are arbitrary positive
numbers, and `phi` gives the last. The code writes `n + 1` for the paper's
number $`m`$ of factors. [dyadicZygmundRectangles](Definitions.lean#L214) uses cubes
from the given grids, with the last side-length exponent prescribed by `Phi`.

For the rounded family, [rounding](Definitions.lean#L147) is the rule
$`\rho(s)=\lceil\log_2 s\rceil+2`$.
[roundedScales](Definitions.lean#L151) retains every tuple obtained by applying
this rule to the continuous side lengths. The first rounded scales may occur
with more than one last scale.
[shiftedCubes](Definitions.lean#L160) gives the explicit shifted grids, and
[roundedRectangles](Definitions.lean#L169) selects their products with these
rounded side lengths.

[initialProjection](Definitions.lean#L76) retains the first factors of a rectangle.
[sliceFamily](Definitions.lean#L100) forms $`\mathcal G_t`$: it projects the members
of $`\mathcal G`$ whose last factor contains $`t`$, counting each projection once.

## Maximal and overlap functions

For a family $`\mathcal G`$, [shadow](Definitions.lean#L87) is the union of its
rectangles and [overlap](Definitions.lean#L93) is the sum of their indicators.
[maximal](Definitions.lean#L130) is the supremum, over rectangles containing
the point, of the averages of $`|f|`$. Its averages use the nonnegative
Lebesgue integral divided by the rectangle's volume.

The maximal and overlap functions may take the value infinity. Lean represents
their values by `ℝ≥0∞`, meaning $`[0,\infty]`$; here `∫⁻`, `∑'` and `⨆` denote
the nonnegative integral, sum and supremum. `ENNReal.ofReal` places a
nonnegative real number in this extended range. The [exp](Definitions.lean#L221)
used for overlap bounds is the usual exponential, with value infinity at infinity.

In these statements, `eLpNorm` denotes the $`L^p`$ norm with respect to
Lebesgue measure, allowing infinity. For $`0<p<\infty`$, a finite value
means precisely that the function is Lebesgue measurable and the integral
of $`|f|^p`$ is finite. `MemLp` asserts that this norm is finite and so
expresses membership in $`L^p`$. `LocallyIntegrable` means membership in
$`L^1_{\mathrm{loc}}`$.

When the input is integrable on each rectangle, the maximal function is
[proved to agree](Proof/OperatorBridge.lean#L26) with the supremum formed
using ordinary real integrals.

The sharpness statement uses finite families and ordinary real integrals.
The [overlap exponential has a finite integral on the shadow](Proof/MeasureBridge.lean#L67).
`Tendsto (fun N => a N) atTop atTop` expresses $`a_N\to+\infty`$ as
$`N\to\infty`$.

## Boundary conventions

The explicit shifted grids in the paper use $`[a,b)`$ in each scalar
coordinate. [cubeIco](Definitions.lean#L182), [rectangleIco](Definitions.lean#L176) and
[maximalIco](Definitions.lean#L205) use that convention directly.
The prescribed-scale covering asserts [IcoGrid](Definitions.lean#L186), which records
the partition and nesting properties of the same cube corners with these
boundaries. The rounded-slice identity uses [sliceFamilyIco](Definitions.lean#L198)
and [overlapIco](Definitions.lean#L193), so its equality holds at every point with
this convention.

Mathlib's boxes use $`(a,b]`$. For locally integrable inputs, Lean proves that
the resulting maximal functions agree
[almost everywhere for the rounded family](Proof/BoundaryBridge.lean#L33)
and [at every point for the continuous family](Proof/BoundaryBridge.lean#L18).
The [continuous maximal function is measurable](Proof/BoundaryBridge.lean#L26).

## Dyadic averages and square functions

[SquareFunctions.lean](SquareFunctions.lean) defines the dyadic operators in
the grouped coordinates above. The notation follows
[Supporting and additional results](../../../SUPPORTING-STATEMENTS.md#averages-and-martingale-differences).

[cubeMean](SquareFunctions.lean#L39) is the signed average $`\langle u\rangle_Q`$,
and [cubeAverage](SquareFunctions.lean#L44) is the operator
$`E_Q u=\mathbf1_Q\langle u\rangle_Q`$.
[cubeDifference](SquareFunctions.lean#L50) is
$`\Delta_Q u=\sum_{J\in\operatorname{ch}(Q)}E_Ju-E_Qu`$.
It uses Mathlib's midpoint subdivision; for grid cubes, this is
[proved to give exactly the dyadic children](../Geometry/CubeGridChildren.lean).

[coordinateAverage](SquareFunctions.lean#L56) and
[coordinateDifference](SquareFunctions.lean#L61) apply these operators in one
coordinate block while holding the others fixed.
[partialAverage](SquareFunctions.lean#L73) and
[partialDifference](SquareFunctions.lean#L85) compose the operators in the
selected coordinates in increasing index order. The empty product is the
identity. Selecting all coordinates gives [fullAverage](SquareFunctions.lean#L79) and
[fullDifference](SquareFunctions.lean#L91).

[signedMaximal](SquareFunctions.lean#L105) is the supremum of
$`|\langle g\rangle_R|`$ over grid rectangles containing the point,
with the absolute value after the average.
[squareFunction](SquareFunctions.lean#L112) is the square root of the sum of
$`|\Delta_Rg|^2`$ over the whole grid. Both functions take values in
$`[0,\infty]`$.
[productMaximal](SquareFunctions.lean#L97) gives the usual supremum of
averages of $`|f|`$ in grouped coordinates.

For the weighted estimates, a top rectangle and a smallest side length
$`2^{-k}`$ determine finite grids.
[bottomCubes](SquareFunctions.lean#L117) are the cubes of that smallest size;
[interiorCubes](SquareFunctions.lean#L124) are the larger grid cubes inside
the top factor. The constancy conditions require the input to be constant
on each bottom cube or product of bottom cubes.
[partialSquareFunction](SquareFunctions.lean#L150) is the square root of
the sum of squared differences in selected coordinates over these interior cubes.
[combinedSquareFunction](SquareFunctions.lean#L158) is
$`Wg=(\sum_j(S_{A_j}g)^2)^{1/2}`$, where $`A_j`$ omits coordinate $`j`$.
The region [partialRectangleRegion](SquareFunctions.lean#L166) is
$`K^A\times I_0^{A^c}`$: selected factors come from $`K`$, and the others
are the top factors.

## The projection and its averaging families

[Projections.lean](Projections.lean) uses the same coordinate operators in
the [finite dyadic setting](../../../SUPPORTING-STATEMENTS.md#finite-dyadic-setting).
[finiteCubes](Projections.lean#L28) and
[finiteRectangles](Projections.lean#L33) include the smallest cubes.

For a family $`\mathcal G`$ in this finite grid,
[projection](Projections.lean#L46) defines $`F_{\mathcal G}`$ by subtracting
from $`f`$ the product martingale differences indexed by interior rectangles
contained in members of $`\mathcal G`$.
[removedRectangles](Projections.lean#L39) is a set, so each removed rectangle
is counted once. Under the finite-setting hypotheses these sums have finitely
many terms; the notation `∑'` is therefore an ordinary finite sum.
For an input supported on the top rectangle and constant on its bottom
rectangles, the [full-grid formula agrees with the finite construction](../Projection/CommonCutoff.lean#L46).

To define a cross-coordinate average, fix the cubes in all coordinates
except $`j`$. [crossCandidates](Projections.lean#L53) collects the $`j`th
factors of members of $`\mathcal G`$ containing those fixed cubes in the
other coordinates, and includes every bottom cube of the top factor.
[crossPartition](Projections.lean#L62) selects the maximal candidates, using
the box order `P ≤ Q` for containment.
They [partition the top factor](../Geometry/ProductPartitions.lean), and
[crossAverage](Projections.lean#L70) averages over this partition in
coordinate $`j`$.

[averagingRectangles](Projections.lean#L80) is the family $`\mathcal B`$:
rectangles in the finite grid with at least one factor belonging to the
cross partition determined by their other factors. These are the averaging
rectangles used in the projected-function estimates.

## Mathlib definitions

For the standard-library definitions, see Mathlib's
[boxes](https://github.com/leanprover-community/mathlib4/blob/1f414401f69059aa7eead47b53ee40bd38455eeb/Mathlib/Analysis/BoxIntegral/Box/Basic.lean#L76),
[midpoint children](https://github.com/leanprover-community/mathlib4/blob/1f414401f69059aa7eead47b53ee40bd38455eeb/Mathlib/Analysis/BoxIntegral/Partition/SubboxInduction.lean#L47),
[product volume](https://github.com/leanprover-community/mathlib4/blob/1f414401f69059aa7eead47b53ee40bd38455eeb/Mathlib/MeasureTheory/Constructions/Pi.lean#L660),
[real integral](https://github.com/leanprover-community/mathlib4/blob/1f414401f69059aa7eead47b53ee40bd38455eeb/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean#L158),
[nonnegative integral](https://github.com/leanprover-community/mathlib4/blob/1f414401f69059aa7eead47b53ee40bd38455eeb/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean#L48),
[extended norms](https://github.com/leanprover-community/mathlib4/blob/1f414401f69059aa7eead47b53ee40bd38455eeb/Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean#L92),
[real powers](https://github.com/leanprover-community/mathlib4/blob/1f414401f69059aa7eead47b53ee40bd38455eeb/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean#L34),
[extended nonnegative powers](https://github.com/leanprover-community/mathlib4/blob/1f414401f69059aa7eead47b53ee40bd38455eeb/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean#L486),
[coordinate replacement](https://github.com/leanprover-community/mathlib4/blob/1f414401f69059aa7eead47b53ee40bd38455eeb/Mathlib/Logic/Function/Basic.lean#L644),
[nonnegative sums](https://github.com/leanprover-community/mathlib4/blob/1f414401f69059aa7eead47b53ee40bd38455eeb/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean#L72),
[general sums](https://github.com/leanprover-community/mathlib4/blob/1f414401f69059aa7eead47b53ee40bd38455eeb/Mathlib/Topology/Algebra/InfiniteSum/Defs.lean),
[maximal elements](https://github.com/leanprover-community/mathlib4/blob/1f414401f69059aa7eead47b53ee40bd38455eeb/Mathlib/Order/Defs/Unbundled.lean#L246), and
[proper subsets of a finite set](https://github.com/leanprover-community/mathlib4/blob/1f414401f69059aa7eead47b53ee40bd38455eeb/Mathlib/Data/Finset/Powerset.lean#L155).
