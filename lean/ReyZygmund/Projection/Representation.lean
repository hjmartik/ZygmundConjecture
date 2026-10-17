import ReyZygmund.Projection.LocalProductExpansion
import ReyZygmund.ToMathlib.Algebra.BigOperators.Powerset

/-!
# Representation on the finite averaging family

The local full-difference sum vanishes below an averaging rectangle. Expanding
the coordinate telescopes and separating the full set of coordinates gives
the exact signed formula.
-/

open BoxIntegral
open scoped BigOperators Classical

namespace ReyZygmund.Projection

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- The finite common-projection representation, summed over proper subsets of
coordinates. -/
theorem finite_representation
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (R : ∀ i, Box (Fin (d i)))
    (hR : R ∈ averagingRectangles I N G)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productRectangle I → F.1 x = 0)
    (x : ProductPoint d) (hx : x ∈ productRectangle R) :
    (productAverageMap Finset.univ R F).1 x =
      ∑ B ∈ ((Finset.univ : Finset (Fin m)).powerset.erase Finset.univ),
        (-1 : ℝ) ^ (m + 1 + B.card) *
          (productAverageMap B R (finiteProjectionMap I N G F)).1 x := by
  let FP := finiteProjectionMap I N G F
  have hc := finiteProjectionMap_productStep_closure I N G F hf hs
  have hzero :
      (∑ L ∈ (productInterior I N).filter (fun L => ∀ i, L i ≤ R i),
        (productDifferenceMap Finset.univ L FP).1 x) = 0 := by
    have h := congrArg (fun T : Module.End ℝ (boundedMeasurableFunctions d) => (T F).1 x)
      (averagingRectangle_difference_sum_vanishes I N hd G R hR)
    simpa [FP, Module.End.mul_apply, Finset.sum_apply] using h
  have hexp := local_product_expansion I N hd R (mem_averagingRectangles.mp hR).1
    FP hc.1 hc.2 x hx
  have hfull :
      (∑ B ∈ (Finset.univ : Finset (Fin m)).powerset,
        (-1 : ℝ) ^ B.card * (productAverageMap B R FP).1 x) = 0 :=
    hexp.symm.trans hzero
  have hpres : (productAverageMap Finset.univ R FP).1 x =
      (productAverageMap Finset.univ R F).1 x := by
    exact congrArg (fun T : Module.End ℝ (boundedMeasurableFunctions d) => (T F).1 x)
      (averagingRectangles_preserved I N hd G R hR)
  rw [← hpres]
  simpa only [Finset.card_univ, Fintype.card_fin, Finset.ssubsets] using
    Finset.eq_sum_ssubsets_of_sum_powerset_eq_zero
      (Finset.univ : Finset (Fin m)) (fun B => (productAverageMap B R FP).1 x) hfull

end ReyZygmund.Projection
