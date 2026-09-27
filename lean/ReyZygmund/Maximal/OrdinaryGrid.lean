import ReyZygmund.Geometry.GridFamilies
import ReyZygmund.Maximal.Forest

/-! # Ordinary finite-grid maximal estimates

Averaging on the smallest cubes preserves each selected average, and Jensen's
inequality controls the input norm. Localization to disjoint top rectangles
removes the requirement of a common top rectangle. The squared L2 factor is `4 ^
m`. Neither incomparability nor sparseness is needed.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- The ordinary finite-grid estimate for integrable inputs, without constancy on the
smallest cubes. -/
theorem finite_ordinary_general_input_integral
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : IntegrableOn f (productBox I) volume)
    (hpow : IntegrableOn (fun x => Real.rpow |f x| p) (productBox I) volume) :
    (∫ x in productBox I, Real.rpow (finiteFunctionMaximal G f x) p) ≤
      Real.rpow (p / (p - 1)) (p * (m : ℝ)) *
        ∫ x in productBox I, Real.rpow |f x| p := by
  let g := leafAverage I N (fun x => |f x|)
  have hg : ProductLeafConstant I N g := productLeafConstant_leafAverage I N _
  have hg0 : ∀ x, 0 ≤ g x :=
    leafAverage_nonneg I N (fun x => |f x|) (fun x _ => abs_nonneg (f x))
  let F := finiteInput I N g hg
  have hF : ProductLeafConstant I N F.1 := productLeafConstant_indicator hg
  have hs : ∀ x, x ∉ productBox I → F.1 x = 0 :=
    fun x hx => Set.indicator_of_notMem hx g
  have hpower : (∫ x in productBox I, Real.rpow (g x) p) ≤
      ∫ x in productBox I, Real.rpow |f x| p := by
    have h := integral_abs_rpow_leafAverage_le I N (fun x => |f x|) p hp.le hf.abs
      (by simpa only [abs_abs] using hpow)
    simpa only [g, abs_abs, abs_of_nonneg (hg0 _)] using h
  have hinput : (∫ x in productBox I, Real.rpow |F.1 x| p) =
      ∫ x in productBox I, Real.rpow (g x) p := by
    apply setIntegral_congr_fun (measurableSet_productBox I)
    intro x hx
    change Real.rpow |(productBox I).indicator g x| p = Real.rpow (g x) p
    rw [Set.indicator_of_mem hx, abs_of_nonneg (hg0 x)]
  rw [finiteFunctionMaximal_leafAverage I N G hG f hf]
  have h := finite_family_maximal_integral I N G hG hd F hF hs p hp
  rw [hinput] at h
  exact h.trans (mul_le_mul_of_nonneg_left hpower
    (Real.rpow_nonneg (div_nonneg (zero_lt_one.trans hp).le (sub_pos.mpr hp).le) _))

/-- Exact ordinary L2 estimate for any finite family in the specified grids,
with an arbitrary L2 input. -/
theorem finite_ordinary_grid_maximal_l2
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : ↑G ⊆ gridRectangles D)
    (f : ProductPoint d → ℝ) (hf : MemLp f 2 volume) :
    (∫ x, (finiteFunctionMaximal G f x) ^ 2) ≤
      (4 : ℝ) ^ m * ∫ x, |f x| ^ 2 := by
  have hpow : Integrable (fun x => |f x| ^ 2) volume := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofNat, Real.rpow_two] using
      hf.integrable_norm_rpow (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have hlocal (R : ∀ i, Box (Fin (d i))) : IntegrableOn f (productBox R) volume := by
    let : IsFiniteMeasure (volume.restrict (productBox R)) :=
      isFiniteMeasure_restrict.mpr (productBox_volume_lt_top R).ne
    exact MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hf.restrict (productBox R))
  have hconstant : Real.rpow ((2 : ℝ) / (2 - 1)) (2 * (m : ℝ)) = (4 : ℝ) ^ m := by
    rw [show (2 : ℝ) - 1 = 1 by norm_num, div_one, Real.rpow_eq_pow]
    rw [show 2 * (m : ℝ) = ((2 * m : ℕ) : ℝ) by push_cast; rfl,
      Real.rpow_natCast, pow_mul]
    norm_num
  obtain ⟨k, N, T, _, hdis, hcover, hcut⟩ := exists_finite_grid_roots D G hG
  have hroot (R : ∀ i, Box (Fin (d i))) (hR : R ∈ T) :
      (∫ x in productBox R,
        (finiteFunctionMaximal (G.filter (fun Q => ∀ i, Q i ≤ R i)) f x) ^ 2) ≤
      (4 : ℝ) ^ m * ∫ x in productBox R, |f x| ^ 2 := by
    have h := finite_ordinary_general_input_integral R (fun _ => N) hd
      (G.filter (fun Q => ∀ i, Q i ≤ R i)) (hcut R hR) f 2 (by norm_num)
      (hlocal R) (by simpa only [Real.rpow_eq_pow, Real.rpow_two] using hpow.integrableOn)
    simpa only [hconstant, Real.rpow_eq_pow, Real.rpow_two] using h
  have hsum : (∑ R ∈ T, ∫ x in productBox R, |f x| ^ 2) ≤ ∫ x, |f x| ^ 2 := by
    rw [← integral_biUnion_finset T (fun R _ => measurableSet_productBox R)
      hdis (fun _ _ => hpow.integrableOn)]
    exact setIntegral_le_integral hpow (Filter.Eventually.of_forall (fun x => sq_nonneg _))
  calc
    _ = ∑ R ∈ T, ∫ x in productBox R,
        (finiteFunctionMaximal (G.filter (fun Q => ∀ i, Q i ≤ R i)) f x) ^ 2 := by
      simpa only [Real.rpow_eq_pow, Real.rpow_two] using
        integral_rpow_finiteFunctionMaximal_forest T G hdis hcover f 2 (by norm_num)
    _ ≤ ∑ R ∈ T, (4 : ℝ) ^ m * ∫ x in productBox R, |f x| ^ 2 :=
      Finset.sum_le_sum hroot
    _ = (4 : ℝ) ^ m * ∑ R ∈ T, ∫ x in productBox R, |f x| ^ 2 :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (pow_nonneg (by norm_num) m)

end ReyZygmund
