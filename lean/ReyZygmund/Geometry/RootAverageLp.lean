import ReyZygmund.Geometry.ProductIntegration
import ReyZygmund.Geometry.ProductAverageProperties
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Lp contraction for top-cube averages

Jensen's inequality for normalized Lebesgue measure gives coefficient one.
Constancy on the smallest cubes gives integrability of the input and its real
powers. Values outside the top rectangle are unrestricted.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Geometry

private theorem box_average_abs_rpow {d : ℕ}
    (I : Box (Fin d)) (N : ℕ) (g : (Fin d → ℝ) → ℝ)
    (hg : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y)
    (p : ℝ) (hp : 1 ≤ p) :
    Real.rpow |(∫ x in (I : Set (Fin d → ℝ)), g x) /
        volume.real (I : Set (Fin d → ℝ))| p ≤
      (∫ x in (I : Set (Fin d → ℝ)), Real.rpow |g x| p) /
        volume.real (I : Set (Fin d → ℝ)) := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hvol := box_volume_pos I
  have hzero : volume (I : Set (Fin d → ℝ)) ≠ 0 := by
    intro hz
    simp [measureReal_def, hz] at hvol
  have ha : IntegrableOn (fun x => |g x|) (I : Set (Fin d → ℝ)) volume := by
    apply integrableOn_of_leafConstant I N
    intro Q hQ x hx y hy
    rw [hg Q hQ x hx y hy]
  have hpow : IntegrableOn (fun x => Real.rpow |g x| p)
      (I : Set (Fin d → ℝ)) volume := by
    apply integrableOn_of_leafConstant I N
    intro Q hQ x hx y hy
    rw [hg Q hQ x hx y hy]
  have hj := (convexOn_rpow hp).map_set_average_le
    (Real.continuous_rpow_const hp0).continuousOn isClosed_Ici hzero
    (I.measure_coe_lt_top volume).ne
    (ae_of_all _ (fun x => abs_nonneg (g x))) ha hpow
  have hj' : Real.rpow
      ((∫ x in (I : Set (Fin d → ℝ)), |g x|) /
        volume.real (I : Set (Fin d → ℝ))) p ≤
      (∫ x in (I : Set (Fin d → ℝ)), Real.rpow |g x| p) /
        volume.real (I : Set (Fin d → ℝ)) := by
    simpa only [setAverage_eq, smul_eq_mul, div_eq_mul_inv, mul_comm,
      Real.rpow_eq_pow] using hj
  apply le_trans (Real.rpow_le_rpow (abs_nonneg _) ?_ hp0) hj'
  rw [abs_div, abs_of_pos hvol]
  exact div_le_div_of_nonneg_right abs_integral_le_integral_abs hvol.le

variable {m : ℕ} {d : Fin m → ℕ}

private theorem update_mem_root (I : ∀ i, Box (Fin (d i)))
    {x : ProductPoint d} (hx : x ∈ productBox I) (j : Fin m)
    {y : Fin (d j) → ℝ} (hy : y ∈ I j) :
    Function.update x j y ∈ productBox I := by
  apply (mem_productBox I _).mpr
  intro i
  by_cases hij : i = j
  · subst i
    simpa using hy
  · simpa [hij] using (mem_productBox I x).mp hx i

/-- Averaging over a top cube contracts the Lp norm with coefficient one, without a
support or positive-dimension assumption. -/
theorem coordinateRootAverage_integral_rpow
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (j : Fin m) (p : ℝ) (hp : 1 ≤ p) :
    (∫ x in productBox I, Real.rpow |(averageMap j (I j) F).1 x| p) ≤
      ∫ x in productBox I, Real.rpow |F.1 x| p := by
  have hroot : I j ∈ descendants (I j) (N j) :=
    mem_descendants.mpr ⟨0, Nat.zero_le _, Prepartition.mem_top.mpr rfl⟩
  have hleaf := productLeafConstant_coordinateAverage hf j (I j) hroot
  have hH : ProductLeafConstant I N
      (fun x => Real.rpow |(averageMap j (I j) F).1 x| p) := by
    intro Q hQ x hx y hy
    exact congrArg (fun a => Real.rpow |a| p) (hleaf Q hQ x hx y hy)
  have hK : ProductLeafConstant I N (fun x => Real.rpow |F.1 x| p) := by
    intro Q hQ x hx y hy
    exact congrArg (fun a => Real.rpow |a| p) (hf Q hQ x hx y hy)
  have h := integral_product_le_of_coordinate_le I N _ _ hH hK
    (fun x _ => Real.rpow_nonneg (abs_nonneg _) p)
    (fun x _ => Real.rpow_nonneg (abs_nonneg _) p) 1 zero_le_one j (by
      intro x hx
      have hs : ∀ Q ∈ leaves (I j) (N j), ∀ y ∈ Q, ∀ z ∈ Q,
          F.1 (Function.update x j y) = F.1 (Function.update x j z) := by
        intro Q hQ y hy z hz
        have hh := productStep_coordinate_leafConstant I N F.1 hf j x Q hQ y hy z hz
        simpa only [Set.indicator_of_mem
          (update_mem_root I hx j ((level (I j) (N j)).le_of_mem hQ hy)),
          Set.indicator_of_mem
          (update_mem_root I hx j ((level (I j) (N j)).le_of_mem hQ hz))] using hh
      have hj := box_average_abs_rpow (I j) (N j)
        (fun y => F.1 (Function.update x j y)) hs p hp
      have heq : (∫ y in (I j : Set (Fin (d j) → ℝ)),
          Real.rpow |(averageMap j (I j) F).1 (Function.update x j y)| p) =
          volume.real (I j : Set (Fin (d j) → ℝ)) *
            Real.rpow |(∫ z in (I j : Set (Fin (d j) → ℝ)),
              F.1 (Function.update x j z)) /
              volume.real (I j : Set (Fin (d j) → ℝ))| p := by
        calc
          _ = ∫ _ in (I j : Set (Fin (d j) → ℝ)),
              Real.rpow |(∫ z in (I j : Set (Fin (d j) → ℝ)),
                F.1 (Function.update x j z)) /
                volume.real (I j : Set (Fin (d j) → ℝ))| p := by
            apply setIntegral_congr_fun (I j).measurableSet_coe
            intro y hy
            simp only [averageMap_apply]
            rw [coordinateAverage_of_mem j (I j) F.1 _ (by simpa using hy)]
            simp only [Function.update_idem]
          _ = _ := by rw [setIntegral_const, smul_eq_mul]
      rw [heq, one_mul]
      simpa only [mul_comm] using (le_div_iff₀ (box_volume_pos (I j))).mp hj)
  simpa only [one_mul] using h

private theorem rootAverage_leaf
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (A : Finset (Fin m)) :
    ProductLeafConstant I N (productAverageMap A I F).1 := by
  induction A using Finset.induction_on with
  | empty => simpa using hf
  | @insert j A hj ih =>
    rw [productAverageMap_insert A j hj I, Module.End.mul_apply, averageMap_apply]
    exact productLeafConstant_coordinateAverage ih j (I j)
      (mem_descendants.mpr ⟨0, Nat.zero_le _, Prepartition.mem_top.mpr rfl⟩)

/-- Averaging over top cubes in any set of coordinates contracts the Lp integral for
real p ≥ 1. The empty set gives the identity. -/
theorem productRootAverage_integral_rpow
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (A : Finset (Fin m)) (p : ℝ) (hp : 1 ≤ p) :
    (∫ x in productBox I, Real.rpow |(productAverageMap A I F).1 x| p) ≤
      ∫ x in productBox I, Real.rpow |F.1 x| p := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert j A hj ih =>
    rw [productAverageMap_insert A j hj I, Module.End.mul_apply]
    exact (coordinateRootAverage_integral_rpow I N (productAverageMap A I F)
      (rootAverage_leaf I N F hf A) j p hp).trans ih

end ReyZygmund.Geometry
