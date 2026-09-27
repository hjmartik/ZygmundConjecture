import ReyZygmund.Projection.LocalProductExpansion

/-!
# Representation on the finite averaging family

The local full-difference sum vanishes below an averaging rectangle. Expanding
the coordinate telescopes and separating the full set of coordinates gives
the exact signed formula. No incomparability is needed for this step.
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
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (x : ProductPoint d) (hx : x ∈ productBox R) :
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
  let S := ∑ B ∈ ((Finset.univ : Finset (Fin m)).powerset.erase Finset.univ),
    (-1 : ℝ) ^ B.card * (productAverageMap B R FP).1 x
  have hsplit : (-1 : ℝ) ^ m * (productAverageMap Finset.univ R FP).1 x + S = 0 := by
    have h := (Finset.add_sum_erase (Finset.univ : Finset (Fin m)).powerset
      (fun B => (-1 : ℝ) ^ B.card * (productAverageMap B R FP).1 x)
      (by simp : (Finset.univ : Finset (Fin m)) ∈ Finset.univ.powerset)).trans hfull
    simpa only [Finset.card_univ, Fintype.card_fin, S] using h
  have hval : (-1 : ℝ) ^ m * (productAverageMap Finset.univ R FP).1 x = -S := by
    linarith
  have hsign : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  have hpres : (productAverageMap Finset.univ R FP).1 x =
      (productAverageMap Finset.univ R F).1 x := by
    have h := congrArg (fun T : Module.End ℝ (boundedMeasurableFunctions d) => (T F).1 x)
      (averagingRectangles_preserved I N hd G R hR)
    exact h
  rw [← hpres]
  calc
    _ = ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) *
        (productAverageMap Finset.univ R FP).1 x := by rw [hsign, one_mul]
    _ = (-1 : ℝ) ^ m *
        ((-1 : ℝ) ^ m * (productAverageMap Finset.univ R FP).1 x) := by ring
    _ = -((-1 : ℝ) ^ m) * S := by rw [hval]; ring
    _ = ∑ B ∈ ((Finset.univ : Finset (Fin m)).powerset.erase Finset.univ),
        -((-1 : ℝ) ^ m) *
          ((-1 : ℝ) ^ B.card * (productAverageMap B R FP).1 x) := by
      exact Finset.mul_sum _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro B _
      simp only [pow_add, pow_one]
      ring

end ReyZygmund.Projection
