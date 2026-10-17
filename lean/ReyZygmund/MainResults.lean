import ReyZygmund.MathlibOnly.Solutions
import ReyZygmund.Maximal.WeaklyIncomparableFinite
import ReyZygmund.Projection.CommonCutoff
import ReyZygmund.Projection.CrossProjection
import ReyZygmund.Geometry.SlicedOverlap

/-!
# Proof library entry point

Importing this module provides the proofs of the three main results and
nineteen supporting results. Their independent statements are in
`MathlibOnly.Statements` and `MathlibOnly.SupportingStatements`.

The arguments are organized as follows.

1. `Maximal.Square`, `Maximal.SquareDistribution` and `Maximal.GlobalSquare`
   bound the signed maximal function by the product square function, using
   density grouping, the `L²` maximal estimate and distribution sums.
2. `Projection.CommonCutoff`, `Projection.PartialAverages`,
   `Projection.AveragingGeometry` and `Projection.CrossProjection` develop
   the finite projection, its averages and its martingale differences.
3. `Weighted.Scalar`, `Weighted.OneCoordinate` and `Weighted.Product` give
   the scalar and weighted square-function estimates. `Weighted.ProjectedRow`
   and `Weighted.ProjectedConjugateEstimate` apply them to the projection.
   `Weighted.MaximalAbsorption` closes the estimate by Hölder and absorption.
4. `Maximal.WeaklyIncomparableFinite` and `Maximal.WeakerBound` give the finite
   maximal estimate. `Maximal.WeakerInput`, `Maximal.WeakerGrid` and
   `Maximal.WeakerGlobal` pass to general inputs and dyadic families.
5. `Overlap.FiniteMoments` and `Overlap.Global` obtain overlap moments from
   the maximal estimate. `Overlap.Exponential` turns them into exponential
   integrability by Chebyshev's inequality and layer cake.
6. `Geometry.PrescribedCover`, `Geometry.RoundedSlices` and
   `Geometry.SlicedOverlap` supply the covering and slicing geometry.
   `Selection.Variational`, `Selection.Shadow`, `Selection.Exponential` and
   `Selection.Endpoint` give the selection and exponential-pairing argument.
   `Continuous.RoundedEndpoint`, `Continuous.Endpoint` and
   `Continuous.DyadicEndpoint` establish the endpoint estimates.

`Overlap.Phi` gives sparse Φ-Zygmund overlap, and `Main.Sharpness` gives the
sharpness construction. The [definition guide](MathlibOnly/DEFINITIONS.md)
explains the geometric and analytic representations.
-/
