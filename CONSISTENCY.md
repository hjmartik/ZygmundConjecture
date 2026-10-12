# Consistency checks of the definitions

[Main theorems](MAIN-STATEMENTS.md) states the six results in full and
links each to its independent Lean statement and definitions. This page
explains how those definitions describe the mathematical objects and how
they are related to the definitions used in the proofs. The identifications
described below are proved in Lean.

Start with the objects occurring in the theorem you want to inspect: cubes,
rectangle families, averages, overlap and maximal functions. The
cross-coordinate averages and projection are constructions used in the proof
and are described afterward. The [independent specification guide](lean/ReyZygmund/MathlibOnly/README.md)
explains how the separate statements are organized and connected to the proofs.

## Cubes and grids

A dyadic grid in $`\mathbb R^{d_i}`$ consists of half-open cubes. At each integer
scale $`k`$, the cubes have side length $`2^k`$ and partition the space; any two
intersecting cubes are nested. The dyadic children of a cube are obtained by
halving each side. The results allow arbitrary such grids, with no assumption
that every finite collection has a common ancestor.

Both descriptions require cubes of the prescribed side length to partition
the space at each scale. The independent specification requires intersecting
cubes to be nested; the proof library requires the usual dyadic children to
belong to the next generation. Lean proves these descriptions equivalent,
preserving the cubes themselves. The scale indices are related by $`n=-k`$.
Standard and shifted grids are constructed explicitly. Within a fixed cube,
its descendants obtained by repeated halving are proved to be exactly the
grid cubes of the corresponding smaller side length.

Lean: [grid used in the proofs](lean/ReyZygmund/Geometry/Grids.lean#L23),
[independent grid definition](lean/ReyZygmund/MathlibOnly/Definitions.lean#L44),
[dyadic children](lean/ReyZygmund/MathlibOnly/Proof/GridBridge.lean#L141),
[equivalence of the two descriptions](lean/ReyZygmund/MathlibOnly/Proof/GridBridge.lean#L220),
[standard grids](lean/ReyZygmund/Geometry/StandardGrid.lean),
[shifted grids](lean/ReyZygmund/Geometry/ShiftedGrid.lean), and
[descendants](lean/ReyZygmund/Geometry/GridDescendants.lean#L67).

## Product coordinates and averages

Write $`\mathbb R^d=\mathbb R^{d_1}\times\cdots\times\mathbb R^{d_m}`$, where
$`d=\sum_i d_i`$. A rectangle is a product $`I=I^1\times\cdots\times I^m`$ of
cubes. Listing the scalar coordinates in order identifies this product space
with $`\mathbb R^d`$. The formalization proves that this identification preserves
Lebesgue measure, rectangles, integrals, averages and norms.

For a cube $`Q`$ in the $`j`$th coordinate, $`E_Q`$ averages in $`x_j`$ over $`Q`$,
leaves the other coordinates unchanged, and is zero when $`x_j\notin Q`$.
Here $`x_j`$ ranges over $`\mathbb R^{d_j}`$. These coordinate averages preserve
measurability. For the signed bounded measurable functions used in the finite
construction, averaging in every coordinate is proved to give exactly
$`E_I f=\mathbf1_I|I|^{-1}\int_I f`$.

Lean: [identification of the coordinates](lean/ReyZygmund/Geometry/Flatten.lean#L21),
[preservation of Lebesgue measure](lean/ReyZygmund/Geometry/Flatten.lean#L54),
[rectangle, integral and norm identities](lean/ReyZygmund/Geometry/FlatRectangles.lean),
[rectangles in the independent statement](lean/ReyZygmund/MathlibOnly/Definitions.lean#L60),
[coordinate averages](lean/ReyZygmund/Geometry/ProductOperators.lean), and
[averaging over a rectangle](lean/ReyZygmund/Geometry/ProductMean.lean#L208).

## Families, overlap and maximal functions

A family is weakly incomparable if there are no members $`I,J`$ with
$`I^i\subsetneq J^i`$ for every $`i`$. Equivalently, a containment $`I\subset J`$
leaves at least one cube factor unchanged: $`I^i=J^i`$ for some $`i`$.
This equivalence is proved in Lean. Ordinary incomparability means that no
distinct members contain one another and implies weak incomparability.
Sparseness means that there are pairwise
disjoint measurable sets $`E_I\subset I`$ with $`|E_I|\geq\eta|I|`$.
These conditions are stated directly in terms of the rectangles and their subsets;
membership in the dyadic grids is a separate hypothesis.

The independent statements allow Lebesgue-measurable sets $`E_I`$.
Each has a Borel subset of the same measure, so replacing these sets
preserves containment, disjointness and the exact value of $`\eta`$.
This proves the equivalence with the formulation using Borel sets in the proofs.
The equivalence and its use in the stated results are formalized.

For a rectangle family $`\mathcal G`$, the overlap counts the rectangles through
a point, and the shadow is their union:

```math
h_{\mathcal G}=\sum_{I\in\mathcal G}\mathbf1_I,
\qquad
\mathrm{sh}(\mathcal G)=\bigcup_{I\in\mathcal G}I.
```

The maximal function is the supremum of the averages of $`|f|`$ over rectangles
containing the point. The specification defines these averages using
nonnegative integrals, which may take the value infinity. The hypotheses of
the maximal estimates ensure integrability on each rectangle. Lean proves
that these averages agree with the ordinary real-valued averages used in
the proofs. Lean also identifies the supremum over rectangles containing the
point with the formulation that assigns each average zero outside its rectangle.

The public maximal and overlap estimates use these possibly infinite quantities
directly. The supporting proofs establish almost-everywhere finiteness under
the hypotheses of the respective $`L^p`$ maximal and sparse overlap estimates.
Lean proves that passing to real-valued representatives preserves the norms
and exponential integrals used in those proofs.

Some intermediate bounds use the exponential minus one. Adding the measure of
the shadow gives the full exponential bounds in the statements, with an enlarged
constant. This conversion is proved in Lean.

Lean: [weak incomparability](lean/ReyZygmund/MathlibOnly/Definitions.lean#L90),
[equivalent containment condition](lean/ReyZygmund/MathlibOnly/Proof/IncomparabilityBridge.lean#L37),
[sparseness](lean/ReyZygmund/MathlibOnly/Definitions.lean#L98),
[incomparability](lean/ReyZygmund/MathlibOnly/Definitions.lean#L84),
[equivalent definitions of sparseness](lean/ReyZygmund/MathlibOnly/Proof/MeasureBridge.lean#L22),
[overlap](lean/ReyZygmund/MathlibOnly/Definitions.lean#L79),
[shadow](lean/ReyZygmund/MathlibOnly/Definitions.lean#L73),
[agreement of the two integral formulas](lean/ReyZygmund/Main/Maximal.lean#L33),
[the independently defined maximal function](lean/ReyZygmund/MathlibOnly/Definitions.lean#L107),
[agreement of the two maximal-function definitions](lean/ReyZygmund/MathlibOnly/Representation.lean#L80),
[norms of the real-valued representatives](lean/ReyZygmund/MathlibOnly/Representation.lean#L97),
[agreement of the exponential integrals](lean/ReyZygmund/MathlibOnly/Representation.lean#L128),
[full exponential bounds](lean/ReyZygmund/MathlibOnly/Proof/IncomparabilityBridge.lean#L52),
and the countable-family arguments for
[maximal functions](lean/ReyZygmund/Maximal/Countable.lean) and
[overlap](lean/ReyZygmund/Overlap/Countable.lean).

The correspondence between the two grid descriptions preserves all products of
grid cubes and all rectangles satisfying the prescribed dyadic side-length
relation. See the [equalities of rectangle families](lean/ReyZygmund/MathlibOnly/Proof/FamilyBridge.lean).

## Continuous rectangles, rounding and measurability

The continuous family $`\mathcal R_\phi`$ consists of rectangles at arbitrary
locations with side lengths
$`(s_1,\ldots,s_{m-1},\phi(s_1,\ldots,s_{m-1}))`$, for all $`s_i>0`$.
The endpoint theorem assumes that $`\phi`$ is positive and coordinatewise
nondecreasing; it requires no continuity or differentiability.

To cover these rectangles by dyadic rectangles, the paper uses
$`\rho(s)=\lceil\log_2s\rceil+2`$ and the corresponding shifted grids.
The rounded family contains every side-length tuple obtained in this way.
The same first $`m-1`$ rounded scales may occur with more than one last scale;
the definition retains all of them. The continuous and rounded families
described independently in the statements are proved to equal those used
in the proofs.

For locally integrable $`f`$, the nonnegative integrals defining the averages
agree with the real integrals, and hence give the same maximal functions.
The paper's shifted grids use $`[a,b)`$ in each scalar coordinate, while
Mathlib's boxes use $`(a,b]`$. Lean proves the following agreements between
the resulting maximal functions and checks measurability:

- For the countable rounded family, the two conventions give
  the same maximal function almost everywhere and the same level-set measures.
- For the continuous family at arbitrary locations, the two conventions give
  the same maximal function at every point. The proof uses continuity under
  translation of the local integrals.
- The continuous maximal function is measurable.

Lean: [continuous rectangles](lean/ReyZygmund/Geometry/PhiRectangles.lean),
[rounding](lean/ReyZygmund/Geometry/RoundedScales.lean),
[equality of the continuous families](lean/ReyZygmund/MathlibOnly/Proof/OperatorBridge.lean#L88),
[shifted cubes](lean/ReyZygmund/MathlibOnly/Definitions.lean#L137),
[equality of the rounded families](lean/ReyZygmund/MathlibOnly/Proof/OperatorBridge.lean#L124),
[agreement of the maximal functions](lean/ReyZygmund/MathlibOnly/Proof/OperatorBridge.lean#L60),
[the independent maximal function with the opposite boundary convention](lean/ReyZygmund/MathlibOnly/Representation.lean#L87),
[the endpoint maximal function](lean/ReyZygmund/Maximal/Euclidean.lean#L21),
[rounded level-set measures](lean/ReyZygmund/MathlibOnly/Proof/MeasureBridge.lean#L72),
[continuous-family boundary equality](lean/ReyZygmund/MathlibOnly/Proof/BoundaryBridge.lean#L18),
and [continuous measurability](lean/ReyZygmund/MathlibOnly/Proof/BoundaryBridge.lean#L26).

## Sharpness integrals

The sharpness construction gives finite families of Euclidean rectangles and
pairwise disjoint subsets establishing their sparseness. For each family,
the overlap is bounded and its shadow has finite measure, so the full
exponential integral over the shadow is finite. The divergence statement says
that these finite values tend to $`+\infty`$ along the sequence of families.
Lean proves that the ordinary real integral and the nonnegative integral give
the same value for each family, and that their formulations of this limiting
statement agree. The public sharpness statement uses a finite sum of indicator
functions and the ordinary real integral. Lean identifies that sum with the
real-valued overlap used in the supporting estimates.

Lean: [the rectangle construction](lean/ReyZygmund/Sharpness/FlatConstruction.lean),
[integrability of the exponential](lean/ReyZygmund/MathlibOnly/Proof/MeasureBridge.lean#L93),
[equality of the integrals](lean/ReyZygmund/MathlibOnly/Proof/MeasureBridge.lean#L109),
[equivalence of the divergence statements](lean/ReyZygmund/MathlibOnly/Proof/MeasureBridge.lean#L118),
[the finite indicator sum](lean/ReyZygmund/MathlibOnly/Representation.lean#L140),
and [full exponential sharpness](lean/ReyZygmund/MathlibOnly/Solutions.lean#L88).

## Cross-coordinate averages and the projection

Fix a rectangle $`I_0=I_0^1\times\cdots\times I_0^m`$. In each coordinate,
take the finite collection of dyadic subcubes of $`I_0^i`$ down to a common smallest size,
including $`I_0^i`$ itself. Let $`\mathcal G`$ be a family of rectangles formed
from these cubes. Fix $`j`$ and choose $`K^i`$ from these collections for $`i\ne j`$.
Collect the cubes $`I^j`$ from those $`I\in\mathcal G`$ for which
$`K^i\subset I^i`$ whenever $`i\ne j`$, and adjoin all the smallest cubes in
$`I_0^j`$. The maximal cubes of this collection partition $`I_0^j`$.
A cube arising from several rectangles is included only once. If no rectangle
contributes a cube, the partition consists of the smallest cubes.

The cross-coordinate average $`X_{K^{A_j}}`$ is the sum of the averaging
operators over this partition, acting in coordinate $`j`$, where
$`A_j=\{1,\ldots,m\}\setminus\{j\}`$. It preserves measurability.

Writing $`\mathrm{ch}(Q)`$ for the dyadic children of $`Q`$, the difference
operators are $`\Delta_Q=\sum_{R\in\mathrm{ch}(Q)}E_R-E_Q`$ and
$`\Delta_{K^A}=\prod_{i\in A}\Delta_{K^i}`$.
For $`f`$ constant on the smallest product cubes and extended by zero outside
$`I_0`$, the projected function $`F`$ is obtained by subtracting the product
martingale differences indexed by subrectangles of members of $`\mathcal G`$,
each counted once. Only finitely many of these differences are nonzero.
The full grid formula for $`F`$ is proved to agree with the finite projection.
The formalization proves the paper's identity

```math
\Delta_{K^{A_j}}F=X_{K^{A_j}}\Delta_{K^{A_j}}f
```

for all the chosen cubes $`K^i`$, including those of the smallest size. This
relates differences of $`F`$ in $`m-1`$ coordinates to an average in the
remaining coordinate.

Lean: [partitions and their averages](lean/ReyZygmund/Geometry/ProductPartitions.lean),
[the full grid sum and finite projection](lean/ReyZygmund/Projection/CommonCutoff.lean#L78),
and [the identity for the projected function](lean/ReyZygmund/Projection/CrossProjection.lean#L47).

## Scope of these checks

The definition review covers the main theorems and the supporting results.
The examples above highlight the principal constructions. Lebesgue measure,
integration, powers and limits use their usual Mathlib definitions.

All six independently stated main results passed Comparator comparison, and their exported proofs and exported dependencies were accepted by Lean’s default kernel, Nanoda and con-ron. Supporting results outside those exports are covered by the ordinary Lean checks described in the [verification guide](VERIFYING.md); their presence in the library does not imply separate Nanoda or con-ron verification.
