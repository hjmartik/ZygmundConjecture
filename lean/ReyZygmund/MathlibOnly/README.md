# Independently inspectable mathematical statements

This independent specification is rebuilt from Mathlib primitives.
[Statements.lean](Statements.lean) gives the three main results;
[SupportingStatements.lean](SupportingStatements.lean) gives nineteen supporting
and additional results. The geometric objects, rectangle families and maximal
and overlap functions are defined in [Definitions.lean](Definitions.lean).
[SquareFunctions.lean](SquareFunctions.lean) defines the averages, martingale
differences and square functions; [Projections.lean](Projections.lean) defines
the finite projection and its averaging families.
These five files import no proof-library module.

To inspect one result, read its statement and the definitions listed below it.
The correctness of the other specifications is not a prerequisite for that
result.

The results concern Henri Martikainen's *The Zygmund conjecture and Rey's
exponential integrability conjecture*. Their mathematical statements appear
in [Main theorems](../../../MAIN-STATEMENTS.md) and
[Supporting and additional results](../../../SUPPORTING-STATEMENTS.md).

The [definition guide](DEFINITIONS.md) explains how these familiar
geometric objects and dyadic operators are represented in Lean, including the
conventions for coordinates, boundaries and integrals.
The [verification guide](../../../VERIFYING.md) records the checking scope, results
and reproduction instructions.

## Main results

| Mathematical statement | Independent statement | Proof of the independent statement |
| --- | --- | --- |
| Weakly incomparable maximal estimate | [WeaklyIncomparableMaximalEstimate](Statements.lean#L34) | [weakly_incomparable_maximal_estimate](Solutions.lean#L31) |
| Rey's conjecture for weakly incomparable families | [WeaklyIncomparableReyConjecture](Statements.lean#L48) | [weakly_incomparable_rey_conjecture](Solutions.lean#L43) |
| Zygmund's conjecture | [ZygmundConjecture](Statements.lean#L66) | [zygmund_conjecture](Solutions.lean#L59) |

## Supporting and additional results

### Square-function estimates

| Mathematical statement | Independent statement | Proof of the independent statement |
| --- | --- | --- |
| Maximal–square-function estimate | [MaximalSquareFunctionEstimate](SupportingStatements.lean#L34) | [maximal_square_function_estimate](Proof/MaximalSquareSolution.lean#L47) |
| Scalar estimate | [ScalarEstimate](SupportingStatements.lean#L47) | [scalar_estimate](Proof/SquareSolutions.lean#L20) |
| One-coordinate weighted square-function estimate | [WeightedSquareFunctionEstimate](SupportingStatements.lean#L55) | [weighted_square_function_estimate](Proof/SquareSolutions.lean#L25) |
| Product weighted square-function estimate | [ProductWeightedSquareFunctionEstimate](SupportingStatements.lean#L72) | [product_weighted_square_function_estimate](Proof/ProductSquareSolution.lean#L22) |

### Projection identities and estimates

| Mathematical statement | Independent statement | Proof of the independent statement |
| --- | --- | --- |
| Preserved averages | [ProjectionPreservesAverages](SupportingStatements.lean#L94) | [projection_preserves_averages](Proof/ProjectionAverageSolutions.lean#L21) |
| Averages in fewer coordinates | [ProjectionPartialAverages](SupportingStatements.lean#L109) | [projection_partial_averages](Proof/ProjectionAverageSolutions.lean#L57) |
| Differences of the projected function | [ProjectionDifferences](SupportingStatements.lean#L126) | [projection_differences](Proof/ProjectionDifferencesSolution.lean#L22) |
| Unchanged projection and weak incomparability | [AveragingFamilyGeometry](SupportingStatements.lean#L143) | [averaging_family_geometry](Proof/AveragingFamilySolutions.lean#L21) |
| Representation of the averages | [RepresentationOfAverages](SupportingStatements.lean#L160) | [representation_of_averages](Proof/AveragingFamilySolutions.lean#L64) |
| Reduction to square functions | [MaximalSquareFunctionReduction](SupportingStatements.lean#L179) | [maximal_square_function_reduction](Proof/ProjectedSquareSolutions.lean#L28) |
| Square-function estimate for the projected function | [ProjectedSquareFunctionEstimate](SupportingStatements.lean#L200) | [projected_square_function_estimate](Proof/ProjectedSquareSolutions.lean#L135) |

### Covering, selection and slicing

| Mathematical statement | Independent statement | Proof of the independent statement |
| --- | --- | --- |
| Prescribed-scale covering | [PrescribedScaleCovering](SupportingStatements.lean#L224) | [prescribed_scale_covering](Proof/CoveringSolution.lean#L15) |
| Córdoba–Fefferman selection | [CordobaFeffermanSelection](SupportingStatements.lean#L238) | [cordoba_fefferman_selection](Proof/SelectionSolution.lean#L19) |
| Weak incomparability of slices | [WeaklyIncomparableSlices](SupportingStatements.lean#L251) | [weakly_incomparable_slices](Proof/SliceSolutions.lean#L20) |
| Half-sparsity of slices | [HalfSparseSlices](SupportingStatements.lean#L267) | [half_sparse_slices](Proof/SliceSolutions.lean#L37) |

### Endpoint, overlap and sharpness results

| Mathematical statement | Independent statement | Proof of the independent statement |
| --- | --- | --- |
| Rounded dyadic endpoint | [RoundedDyadicEndpointEstimate](SupportingStatements.lean#L281) | [rounded_dyadic_endpoint_estimate](Solutions.lean#L68) |
| Dyadic Zygmund conjecture | [DyadicZygmundConjecture](SupportingStatements.lean#L296) | [dyadic_zygmund_conjecture](Proof/DyadicEndpointSolution.lean#L18) |
| Sparse Φ-Zygmund overlap | [SparsePhiZygmundOverlapEstimate](SupportingStatements.lean#L308) | [sparse_phi_zygmund_overlap_estimate](Solutions.lean#L77) |
| Sharpness for the classical dyadic Zygmund family | [ClassicalDyadicZygmundSharpness](SupportingStatements.lean#L324) | [classical_dyadic_zygmund_sharpness](Solutions.lean#L94) |

All propositions in the tables are in the namespace `ReyZygmund.MathlibOnly`.

## Definitions for each result

Each list includes the definitions needed to understand the statement, including those used indirectly.
Mathlib supplies boxes, finite products, Lebesgue measure, integrals, norms,
orders, powers, finite sets, sums and suprema. The source comments explain the
Lean notation and the conventions relevant to these statements.

### Weakly incomparable maximal estimate

[Point](Definitions.lean#L37), [Rectangle](Definitions.lean#L41), [CubeGrid](Definitions.lean#L45), [rectangle](Definitions.lean#L61),
[gridRectangles](Definitions.lean#L80), [WeaklyIncomparable](Definitions.lean#L112), [maximal](Definitions.lean#L130).

<a id="sparse-weakly-incomparable-overlap-estimate"></a>

### Rey's conjecture for weakly incomparable families

[Point](Definitions.lean#L37), [Rectangle](Definitions.lean#L41), [CubeGrid](Definitions.lean#L45), [rectangle](Definitions.lean#L61),
[gridRectangles](Definitions.lean#L80), [shadow](Definitions.lean#L87), [overlap](Definitions.lean#L93),
[WeaklyIncomparable](Definitions.lean#L112), [Sparse](Definitions.lean#L120), [exp](Definitions.lean#L221).

### Zygmund's conjecture

[Point](Definitions.lean#L37), [Rectangle](Definitions.lean#L41), [rectangle](Definitions.lean#L61), [maximal](Definitions.lean#L130),
[zygmundRectangles](Definitions.lean#L139).

<a id="maximal-square-function-estimate"></a>

### Maximal–square-function estimate

- Geometry: [Rectangle](Definitions.lean#L41), [CubeGrid](Definitions.lean#L45), [gridRectangles](Definitions.lean#L80), [ProductPoint](SquareFunctions.lean#L31), [productRectangle](SquareFunctions.lean#L34).
- Martingale differences: [cubeMean](SquareFunctions.lean#L39), [cubeAverage](SquareFunctions.lean#L44), [cubeDifference](SquareFunctions.lean#L50), [coordinateDifference](SquareFunctions.lean#L61), [PartialRectangle](SquareFunctions.lean#L67), [partialDifference](SquareFunctions.lean#L85), [fullDifference](SquareFunctions.lean#L91).
- Maximal and square functions: [signedMaximal](SquareFunctions.lean#L105), [squareFunction](SquareFunctions.lean#L112).

The maximal function takes the absolute value after the signed average.
The square function and maximal function use the whole grid.

### Scalar estimate

Only real numbers, their order, arithmetic and real powers are used.

### One-coordinate weighted square-function estimate

[CubeGrid](Definitions.lean#L45), [cubeMean](SquareFunctions.lean#L39), [cubeAverage](SquareFunctions.lean#L44),
[cubeDifference](SquareFunctions.lean#L50), [bottomCubes](SquareFunctions.lean#L117), [interiorCubes](SquareFunctions.lean#L124),
[ConstantOnBottomCubes](SquareFunctions.lean#L129).

The smallest side length is `2^(-k)`. The sum excludes that bottom scale;
the functions are constant on its cubes, and the weight is strictly positive.

### Product weighted square-function estimate

- Geometry: [Rectangle](Definitions.lean#L41), [CubeGrid](Definitions.lean#L45), [ProductPoint](SquareFunctions.lean#L31), [productRectangle](SquareFunctions.lean#L34), [PartialRectangle](SquareFunctions.lean#L67).
- Coordinate operators: [cubeMean](SquareFunctions.lean#L39), [cubeAverage](SquareFunctions.lean#L44), [cubeDifference](SquareFunctions.lean#L50), [coordinateAverage](SquareFunctions.lean#L56), [coordinateDifference](SquareFunctions.lean#L61), [partialAverage](SquareFunctions.lean#L73), [partialDifference](SquareFunctions.lean#L85).
- Finite grids and integration regions: [bottomCubes](SquareFunctions.lean#L117), [interiorCubes](SquareFunctions.lean#L124), [ConstantOnBottomRectangles](SquareFunctions.lean#L135), [partialInterior](SquareFunctions.lean#L142), [partialRectangleRegion](SquareFunctions.lean#L166).

The same cutoff is used in every coordinate. `partialAverage` and
`partialDifference` compose the coordinate operators in increasing index order.
The integration region uses the selected cubes and the remaining top factors.
The partial average in the denominator remains a function of the unselected
coordinates.

### Common projection definitions

The projection identities and estimates use the following definitions:

- Geometry: [Rectangle](Definitions.lean#L41), [CubeGrid](Definitions.lean#L45), [ProductPoint](SquareFunctions.lean#L31), [productRectangle](SquareFunctions.lean#L34), [PartialRectangle](SquareFunctions.lean#L67).
- Martingale differences: [cubeMean](SquareFunctions.lean#L39), [cubeAverage](SquareFunctions.lean#L44), [cubeDifference](SquareFunctions.lean#L50), [coordinateDifference](SquareFunctions.lean#L61), [partialDifference](SquareFunctions.lean#L85), [fullDifference](SquareFunctions.lean#L91).
- Finite grids and the input: [bottomCubes](SquareFunctions.lean#L117), [interiorCubes](SquareFunctions.lean#L124), [ConstantOnBottomRectangles](SquareFunctions.lean#L135), [finiteCubes](Projections.lean#L28), [finiteRectangles](Projections.lean#L33).
- Projection: [removedRectangles](Projections.lean#L39), [projection](Projections.lean#L46).

The input function is positive on the top rectangle, zero outside it, and constant on
products of smallest cubes. The projection subtracts each removed martingale
difference once and does not need to be positive.

### Preserved averages

Read the [common projection definitions](#common-projection-definitions), together
with [WeaklyIncomparable](Definitions.lean#L112), [coordinateAverage](SquareFunctions.lean#L56),
[partialAverage](SquareFunctions.lean#L73) and [fullAverage](SquareFunctions.lean#L79).

This identity preserves the full averages of the input on the specified family.

### Averages in fewer coordinates

Read the [common projection definitions](#common-projection-definitions), together
with [coordinateAverage](SquareFunctions.lean#L56), [partialAverage](SquareFunctions.lean#L73)
and [fullAverage](SquareFunctions.lean#L79).

`Finset.univ.ssubsets` lists the proper subsets of all
coordinates. The empty subset is included; its averaging operator is the
identity. The formula holds on each rectangle of the family, without an
incomparability hypothesis.

### Differences of the projected function

Read the [common projection definitions](#common-projection-definitions), together
with [coordinateAverage](SquareFunctions.lean#L56), [crossCandidates](Projections.lean#L53),
[crossPartition](Projections.lean#L62) and [crossAverage](Projections.lean#L70).

`Finset.univ.erase j` selects all coordinates except `j`. The partial rectangle
has exactly these factors, each of which may be a smallest cube. The cross
average acts in the omitted coordinate. The identity is pointwise everywhere.

### Unchanged projection and weak incomparability

Read the [common projection definitions](#common-projection-definitions), together
with [WeaklyIncomparable](Definitions.lean#L112), [crossCandidates](Projections.lean#L53),
[crossPartition](Projections.lean#L62) and [averagingRectangles](Projections.lean#L80).

The enlarged family is the union of the original family and the averaging
rectangles. The enlargement leaves the projection unchanged. If the original
family is weakly incomparable, so is the enlarged family.

### Representation of the averages

Read the definitions for [unchanged projection and weak incomparability](#unchanged-projection-and-weak-incomparability),
together with [coordinateAverage](SquareFunctions.lean#L56),
[partialAverage](SquareFunctions.lean#L73) and [fullAverage](SquareFunctions.lean#L79).

The full average on the left acts on `f`; the partial averages on the right
act on its projection. The identity holds on every rectangle of the enlarged
family.

### Reduction to square functions

Read the definitions for [unchanged projection and weak incomparability](#unchanged-projection-and-weak-incomparability),
together with [productMaximal](SquareFunctions.lean#L97),
[partialInterior](SquareFunctions.lean#L142), [partialSquareFunction](SquareFunctions.lean#L150)
and [combinedSquareFunction](SquareFunctions.lean#L158).

`productMaximal` is the supremum of averages of `|f|` in grouped coordinates.
`combinedSquareFunction` is `W F`: the square root of the sum of squares of
the `m` partial square functions obtained by omitting one coordinate at a time.

### Square-function estimate for the projected function

Read the [common projection definitions](#common-projection-definitions), together
with [crossCandidates](Projections.lean#L53), [crossPartition](Projections.lean#L62),
[averagingRectangles](Projections.lean#L80), [productMaximal](SquareFunctions.lean#L97),
[partialInterior](SquareFunctions.lean#L142), [partialSquareFunction](SquareFunctions.lean#L150)
and [combinedSquareFunction](SquareFunctions.lean#L158).

The maximal function in the denominator uses only the averaging rectangles.
This estimate does not require weak incomparability.

### Prescribed-scale covering

[CubeGrid](Definitions.lean#L45), [rounding](Definitions.lean#L147), [shiftedCubes](Definitions.lean#L160), [cubeIco](Definitions.lean#L182), [IcoGrid](Definitions.lean#L186).

The family of grids is indexed by `Fin d → Fin 3`, giving three choices
in each of the `d` scalar coordinates. The grids are chosen before the cube
to be covered. The covering cube belongs to scale `rounding s`, so its side
is exactly `2 ^ rounding s`. The closed input cube is covered, including
its boundary; `IcoGrid` records the grid properties for `[lower, upper)` cubes.

<a id="córdoba-fefferman-selection"></a>

### Córdoba–Fefferman selection

[Point](Definitions.lean#L37), [Rectangle](Definitions.lean#L41), [CubeGrid](Definitions.lean#L45), [rectangle](Definitions.lean#L61), [gridRectangles](Definitions.lean#L80), [shadow](Definitions.lean#L87).

`F.Finite` says that the family is finite. `G \ {R}` removes `R` from
the selected family. The constant depends only on the number of factors.

### Weak incomparability of slices

[Point](Definitions.lean#L37), [Rectangle](Definitions.lean#L41), [rectangleIco](Definitions.lean#L176), [cubeIco](Definitions.lean#L182), [initialProjection](Definitions.lean#L76), [appendLastPoint](Definitions.lean#L69), [overlapIco](Definitions.lean#L193), [sliceFamilyIco](Definitions.lean#L198), [rounding](Definitions.lean#L147), [roundedScales](Definitions.lean#L151), [shiftedCubes](Definitions.lean#L160), [roundedRectangles](Definitions.lean#L169).

`appendLastPoint x t` is the point `(x,t)`. The slice is a set of projected
rectangles. Incomparability and weak incomparability are written out using
the same `[lower, upper)` sets as the slices and overlap. `∃! R` means that
exactly one original rectangle has the stated properties.

### Half-sparsity of slices

[Point](Definitions.lean#L37), [Rectangle](Definitions.lean#L41), [CubeGrid](Definitions.lean#L45), [rectangle](Definitions.lean#L61), [gridRectangles](Definitions.lean#L80), [shadow](Definitions.lean#L87), [initialProjection](Definitions.lean#L76), [sliceFamily](Definitions.lean#L100), [Sparse](Definitions.lean#L120).

The family is finite and satisfies the displayed overlap condition.
For each slice, `Sparse` asserts the existence of the required disjoint
measurable sets.

### Rounded dyadic endpoint

[Point](Definitions.lean#L37), [Rectangle](Definitions.lean#L41), [rounding](Definitions.lean#L147),
[roundedScales](Definitions.lean#L151), [shiftedCubes](Definitions.lean#L160), [roundedRectangles](Definitions.lean#L169),
[rectangleIco](Definitions.lean#L176), [maximalIco](Definitions.lean#L205).

### Dyadic Zygmund conjecture

[Point](Definitions.lean#L37), [Rectangle](Definitions.lean#L41), [CubeGrid](Definitions.lean#L45), [rectangle](Definitions.lean#L61), [maximal](Definitions.lean#L130), [dyadicZygmundRectangles](Definitions.lean#L214).

### Sparse Φ-Zygmund overlap

[Point](Definitions.lean#L37), [Rectangle](Definitions.lean#L41), [CubeGrid](Definitions.lean#L45), [rectangle](Definitions.lean#L61),
[shadow](Definitions.lean#L87), [overlap](Definitions.lean#L93), [Sparse](Definitions.lean#L120), [dyadicZygmundRectangles](Definitions.lean#L214),
[exp](Definitions.lean#L221).

### Sharpness for the classical dyadic Zygmund family

[Point](Definitions.lean#L37), [Rectangle](Definitions.lean#L41), [CubeGrid](Definitions.lean#L45), [rectangle](Definitions.lean#L61),
[shadow](Definitions.lean#L87), [Incomparable](Definitions.lean#L106), [Sparse](Definitions.lean#L120),
[dyadicZygmundRectangles](Definitions.lean#L214).
