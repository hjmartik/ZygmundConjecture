import ReyZygmund.MathlibOnly.SubmittedSolutions
import ReyZygmund.Maximal.SubmittedFinite
import ReyZygmund.Projection.SubmittedGrid
import ReyZygmund.Projection.SubmittedCross
import ReyZygmund.Geometry.SlicedOverlap

/-!
# Main results and proof organization

This is the main entry point. The six independent
propositions are in `MathlibOnly.SubmittedStatements`; their proofs are in
`MathlibOnly.SubmittedSolutions`. The specification imports only Mathlib and
its independent definitions. Proof modules identify those definitions with the
operators used in the proofs.

## Proof route

1. `Maximal.Square`, `SquareDistribution`, and `GlobalSquare` prove the square estimate
   by density grouping, the ordinary L² maximal estimate, and distribution sums.
2. `Projection.SubmittedGrid` identifies the common absolute cutoff with the
   finite descendant model and identifies the full-grid projection with its
   finitely supported sum. `Maximal.WeakIncomparability` proves preservation
   of original averages, the arbitrary-family lower-coordinate formula, the
   enlarged-family geometry, and the signed representation, in that order.
   `Projection.SubmittedCross` includes cubes at the smallest selected scale.
3. `Maximal.SubmittedFinite` turns that representation into a maximal-to-square
   estimate. `Weighted.Scalar`, `OneCoordinate`, `Product`, and `ProjectedRow`
   supply the weighted estimate. `Weighted.SubmittedProjected` performs the
   paper's final comparison with p′ before Hölder; `SubmittedAbsorption`
   retains the intermediate exponent `(m - 1) / p` before the final bound.
4. `Maximal.WeakerBound` expresses the finite weakly incomparable estimate in the
   equal-factor formulation. `WeakerInput`, `WeakerGrid`, and `WeakerGlobal`
   extend it to general inputs and dyadic families using averages on the smallest
   cubes, positive perturbation, disjoint top cubes, and countable exhaustion.
   The maximal estimate is proved independently of the overlap bounds.
5. `Overlap.FiniteMoments` and `Global` obtain overlap moments from the maximal
   estimate. `Overlap.Exponential` uses `MomentTailExponential`: Chebyshev at a
   real moment order, a trivial small-threshold bound, and layer cake. The
   independent statement includes the constant term in the full exponential.
6. `Geometry.PrescribedCover`, `RoundedSlices`, and `SlicedOverlap` provide the
   continuous-to-rounded geometry and the unrestricted sliced-overlap identity.
   `Selection.Variational`, `Shadow`, `Exponential`, and `Endpoint` carry out
   the selection and exponential-pairing argument. `Continuous.RoundedEndpoint`
   and `Continuous.Endpoint` pass to the full operators. `Continuous.DyadicEndpoint`
   gives the paper's unlabelled dyadic consequence.

`Overlap.Phi` proves the sparse prescribed-scale overlap estimate.
`Main.Sharpness` supplies the sequence of finite families in the quantified
sharpness statement.

## Representation conventions

The finite code permits separate depths in each coordinate; `SubmittedGrid`
proves their exact relation to the paper's common cutoff. Rectangles use Mathlib's
Ioc convention. The existing convention bridges give the corresponding Ico
continuous result pointwise and the rounded result almost everywhere.
`MathlibOnly.SubmittedMeasure` proves the equivalence of Lebesgue-measurable
and Borel subsets establishing sparseness, applies the rounded boundary
comparison, and identifies the real and nonnegative sharpness integrals.
These connections are used in the six independent proofs.
The scalar Hessian argument uses a convex supporting line to integrate its
second-derivative bound. This is an explicit local reformulation of the paper's
double integration.
-/
