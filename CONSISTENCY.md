# Consistency checks of the definitions

[Main theorems](MAIN-STATEMENTS.md) states the seven results in full and
links each to its independent Lean statement and definitions. This page
explains how those definitions describe the mathematical objects and how
they are related to the definitions used in the proofs. It records which
identifications have been proved in Lean and which have been checked
mathematically.

Start with the objects occurring in the theorem you want to inspect: cubes,
rectangle families, averages, overlap and maximal functions. The
cross-coordinate averages and projection are constructions used in the proof
and are described afterward. The [independent-statement guide](lean/ReyZygmund/MathlibOnly/README.md)
explains how the separate statements are organized and connected to the proofs.

## Cubes and grids

A dyadic grid in $`\mathbb R^{d_i}`$ consists of half-open cubes. At each integer
scale $`k`$, the cubes have side length $`2^k`$ and partition the space; any two
intersecting cubes are nested. The dyadic children of a cube are obtained by
halving each side. The results allow arbitrary such grids, with no assumption
that every finite collection has a common ancestor.

The proofs and the independent statements describe a grid in two equivalent
ways: one requires the usual dyadic children, while the other requires nesting
of intersecting cubes. Their equivalence has been proved for every grid, keeping
the cubes themselves unchanged. The only difference in indexing is that the
proofs use generation $`n=-k`$. Standard and shifted grids are constructed
explicitly. Within a fixed cube, its descendants obtained by repeated halving
are proved to be exactly the grid cubes of the corresponding smaller side length.

Lean: [grid used in the proofs](lean/ReyZygmund/Geometry/Grids.lean#L23),
[independent grid definition](lean/ReyZygmund/MathlibOnly/Definitions.lean#L31),
[dyadic children](lean/ReyZygmund/MathlibOnly/GridBridge.lean#L141),
[equivalence of the two descriptions](lean/ReyZygmund/MathlibOnly/GridBridge.lean#L220),
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
[rectangles in the independent statement](lean/ReyZygmund/MathlibOnly/OperatorBridge.lean#L26),
[coordinate averages](lean/ReyZygmund/Geometry/ProductOperators.lean), and
[averaging over a rectangle](lean/ReyZygmund/Geometry/ProductMean.lean#L208).

## Families, overlap and maximal functions

A family is incomparable if no distinct members contain one another. The weaker
containment condition says that $`I\subset J`$ leaves at least one cube factor
unchanged: $`I^i=J^i`$ for some $`i`$. Sparseness means that there are pairwise
disjoint measurable sets $`E_I\subset I`$ with $`|E_I|\geq\eta|I|`$.
These conditions are stated directly in terms of the rectangles and their subsets.

The definitions in Lean take the sets $`E_I`$ to be Borel measurable. This gives
the usual Lebesgue-measurable notion of sparseness: each Lebesgue-measurable
$`E_I`$ has a Borel subset of the same measure, so replacing the sets this way
preserves containment, disjointness and the value of $`\eta`$. This measure-theoretic
argument has been reviewed but is not itself a separate Lean theorem here.
The proved equivalence between the two Lean definitions compares their Borel
formulations.

For a rectangle family $`\mathcal G`$, the overlap counts the rectangles through
a point, and the shadow is their union:

```math
h_{\mathcal G}=\sum_{I\in\mathcal G}\mathbf1_I,
\qquad
\operatorname{sh}(\mathcal G)=\bigcup_{I\in\mathcal G}I.
```

The maximal function is the supremum of the averages of $`|f|`$ over rectangles
containing the point. Nonnegative sums, integrals and suprema are allowed to
be infinite. Where the proofs use real-valued averages, their agreement with
the nonnegative-integral definition is proved using the required integrability.
The passage from finite to countable families includes almost-everywhere
finiteness under the hypotheses of the corresponding estimates; this justifies
the real-valued functions used in the norm and integral estimates.

Lean: [conditions on the families](lean/ReyZygmund/MathlibOnly/Definitions.lean#L66),
[equivalent definitions of sparseness](lean/ReyZygmund/MathlibOnly/OperatorBridge.lean#L44),
[overlap](lean/ReyZygmund/MathlibOnly/OperatorBridge.lean#L40),
[shadow](lean/ReyZygmund/MathlibOnly/OperatorBridge.lean#L36),
[agreement of the two integral formulas](lean/ReyZygmund/Main/Maximal.lean#L33),
[the independently defined maximal function](lean/ReyZygmund/MathlibOnly/OperatorBridge.lean#L54),
and the countable-family arguments for
[maximal functions](lean/ReyZygmund/Maximal/Countable.lean) and
[overlap](lean/ReyZygmund/Overlap/Countable.lean).

The correspondence between the two grid descriptions preserves all products of
grid cubes and all rectangles satisfying the prescribed dyadic side-length
relation. See the [equalities of rectangle families](lean/ReyZygmund/MathlibOnly/FamilyBridge.lean).

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
Their measurability and boundary conventions are also checked:

- For the countable rounded family, using $`[a,b)`$ instead of $`(a,b]`$ in each
  scalar coordinate gives the same maximal function almost everywhere.
- For the continuous family at arbitrary locations, the two conventions give
  the same maximal function at every point. The proof uses continuity under
  translation of the local integrals.
- The continuous maximal function is measurable.

Lean: [continuous rectangles](lean/ReyZygmund/Geometry/PhiRectangles.lean),
[rounding](lean/ReyZygmund/Geometry/RoundedScales.lean),
[equality of the continuous families](lean/ReyZygmund/MathlibOnly/OperatorBridge.lean#L88),
[shifted cubes](lean/ReyZygmund/MathlibOnly/OperatorBridge.lean#L100),
[equality of the rounded families](lean/ReyZygmund/MathlibOnly/OperatorBridge.lean#L124),
[agreement of the maximal functions](lean/ReyZygmund/MathlibOnly/OperatorBridge.lean#L60),
[the endpoint maximal function](lean/ReyZygmund/Maximal/Euclidean.lean#L21),
[rounded-family boundary equality](lean/ReyZygmund/MathlibOnly/BoundaryBridge.lean#L33),
[continuous-family boundary equality](lean/ReyZygmund/MathlibOnly/BoundaryBridge.lean#L18),
and [continuous measurability](lean/ReyZygmund/MathlibOnly/BoundaryBridge.lean#L26).

## Sharpness integrals

The sharpness construction gives finite families of Euclidean rectangles and
pairwise disjoint subsets establishing their sparseness. For each family,
the exponential integral of its overlap over the shadow is finite.
The formalization proves that the nonnegative integral in the statement equals
this ordinary real integral, and that divergence as the family varies has the
same meaning in both formulations.

Lean: [the rectangle construction](lean/ReyZygmund/Sharpness/FlatConstruction.lean),
[equality of the integrals](lean/ReyZygmund/Sharpness/FiniteIntegral.lean#L63),
and [equivalence of the divergence statements](lean/ReyZygmund/Sharpness/FiniteIntegral.lean#L85).

## Cross-coordinate averages and the projection

Fix a rectangle $`I_0=I_0^1\times\cdots\times I_0^m`$. In each coordinate,
take the finite collection of dyadic subcubes of $`I_0^i`$ down to a fixed smallest size,
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

Writing $`\operatorname{ch}(Q)`$ for the dyadic children of $`Q`$, the difference
operators are $`\Delta_Q=\sum_{R\in\operatorname{ch}(Q)}E_R-E_Q`$ and
$`\Delta_{K^A}=\prod_{i\in A}\Delta_{K^i}`$.
For $`f`$ constant on the smallest product cubes and extended by zero outside
$`I_0`$, the projected function $`F`$ is obtained by subtracting the product
martingale differences indexed by subrectangles of members of $`\mathcal G`$,
each counted once. The formalization proves the paper's identity

```math
\Delta_{K^{A_j}}F=X_{K^{A_j}}\Delta_{K^{A_j}}f
```

for the cubes $`K^i`$ above the smallest size. This relates differences of $`F`$
in $`m-1`$ coordinates to an average in the remaining coordinate.

Lean: [partitions and their averages](lean/ReyZygmund/Geometry/ProductPartitions.lean)
and [the identity for the projected function](lean/ReyZygmund/Projection/CommonProjection.lean#L105).

## Scope of these checks

The definition review covers the main theorems and the supporting results.
The examples above highlight the principal constructions. Lebesgue measure,
integration, powers and limits use their usual Mathlib definitions.

All seven independently stated main results passed Comparator comparison and
proof checking by Lean and Nanoda. Some additional results discussed here,
including the boundary-convention results, were reviewed and checked by Lean
but were not part of those Nanoda checks. The [verification guide](VERIFYING.md)
records the exact coverage, including ordinary Lean replay.
