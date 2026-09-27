import ReyZygmund.Geometry.GridFamilies
import ReyZygmund.Maximal.Forest
import ReyZygmund.Maximal.WeakerInput

/-! # The finite weaker-containment estimate on arbitrary grids

The grid geometry places the finite family in pairwise disjoint top rectangles.
Summing their p-th power estimates preserves the dimension-only norm constant and
the dependence `(p / (p - 1)) ^ (m - 1)`.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

private theorem power_bound_of_root_bound {A B C p : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hp : 0 < p)
    (h : Real.rpow A (1 / p) ≤ C * Real.rpow B (1 / p)) :
    A ≤ Real.rpow C p * B := by
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hA _) h hp.le
  simp only [Real.rpow_eq_pow, one_div] at hh ⊢
  rw [Real.rpow_inv_rpow hA hp.ne',
    Real.mul_rpow hC (Real.rpow_nonneg hB _), Real.rpow_inv_rpow hB hp.ne'] at hh
  exact hh

private theorem root_bound_of_power_bound {A B C p : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hp : 0 < p)
    (h : A ≤ Real.rpow C p * B) :
    Real.rpow A (1 / p) ≤ C * Real.rpow B (1 / p) := by
  have hh := Real.rpow_le_rpow hA h (one_div_nonneg.mpr hp.le)
  simp only [Real.rpow_eq_pow, one_div] at hh ⊢
  rw [Real.mul_rpow (Real.rpow_nonneg hC p) hB,
    Real.rpow_rpow_inv hC hp.ne'] at hh
  exact hh

/-- Global p-th power bound for a finite weaker-containment family of grid
rectangles and an arbitrary Lp input. No bounded support is required. -/
theorem finite_weaker_grid_maximal_integral
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : ↑G ⊆ gridRectangles D)
    (hweak : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → ∃ i, R i = S i)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    (∫ x, Real.rpow (finiteFunctionMaximal G f x) p) ≤
      Real.rpow ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1)) p *
          ∫ x, Real.rpow |f x| p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpE : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have hpow : Integrable (fun x => Real.rpow |f x| p) volume := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le, Real.rpow_eq_pow] using
      hf.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
  have hlocal (R : ∀ i, Box (Fin (d i))) : IntegrableOn f (productBox R) volume := by
    let : IsFiniteMeasure (volume.restrict (productBox R)) :=
      isFiniteMeasure_restrict.mpr (productBox_volume_lt_top R).ne
    exact MemLp.integrable hpE (hf.restrict (productBox R))
  let C : ℝ := (maximalDimensionConstant d + 3) * (p / (p - 1)) ^ (m - 1)
  have hC : 0 ≤ C := by
    have hK : 0 ≤ maximalDimensionConstant d := by
      unfold maximalDimensionConstant
      exact sq_nonneg _
    exact mul_nonneg (add_nonneg hK (by norm_num))
      (pow_nonneg (div_nonneg hp0.le (sub_pos.mpr hp).le) _)
  obtain ⟨k, N, T, _, hdis, hcover, hcut⟩ := exists_finite_grid_roots D G hG
  have hroot (R : ∀ i, Box (Fin (d i))) (hR : R ∈ T) :
      (∫ x in productBox R,
        Real.rpow (finiteFunctionMaximal (G.filter (fun Q => ∀ i, Q i ≤ R i)) f x) p) ≤
      Real.rpow C p * ∫ x in productBox R, Real.rpow |f x| p := by
    have hi : ∀ Q ∈ G.filter (fun Q => ∀ i, Q i ≤ R i),
        ∀ S ∈ G.filter (fun Q => ∀ i, Q i ≤ R i), (∀ i, Q i ≤ S i) → ∃ i, Q i = S i :=
      fun Q hQ S hS => hweak Q (Finset.mem_filter.mp hQ).1 S (Finset.mem_filter.mp hS).1
    have h := finite_weaker_general_input_norm hm R (fun _ => N) hd
      (G.filter (fun Q => ∀ i, Q i ≤ R i)) (hcut R hR) hi f p hp
      (hlocal R) hpow.integrableOn
    change Real.rpow _ (1 / p) ≤ C * Real.rpow _ (1 / p) at h
    have hA : 0 ≤ ∫ x in productBox R,
        Real.rpow (finiteFunctionMaximal (G.filter (fun Q => ∀ i, Q i ≤ R i)) f x) p :=
      integral_nonneg (fun x => Real.rpow_nonneg (finiteFunctionMaximal_nonneg _ f x) p)
    have hB : 0 ≤ ∫ x in productBox R, Real.rpow |f x| p :=
      integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) p)
    exact power_bound_of_root_bound hA hB hC hp0 h
  have hsum : (∑ R ∈ T, ∫ x in productBox R, Real.rpow |f x| p) ≤
      ∫ x, Real.rpow |f x| p := by
    rw [← integral_biUnion_finset T (fun R _ => measurableSet_productBox R)
      hdis (fun _ _ => hpow.integrableOn)]
    exact setIntegral_le_integral hpow
      (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (abs_nonneg _) p))
  calc
    _ = ∑ R ∈ T, ∫ x in productBox R,
        Real.rpow (finiteFunctionMaximal (G.filter (fun Q => ∀ i, Q i ≤ R i)) f x) p :=
      integral_rpow_finiteFunctionMaximal_forest T G hdis hcover f p hp0
    _ ≤ ∑ R ∈ T, Real.rpow C p * ∫ x in productBox R, Real.rpow |f x| p :=
      Finset.sum_le_sum hroot
    _ = Real.rpow C p * ∑ R ∈ T, ∫ x in productBox R, Real.rpow |f x| p :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hC p)

/-- Taking the real p-th root leaves exactly the announced norm constant. -/
theorem finite_weaker_grid_maximal_norm
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : ↑G ⊆ gridRectangles D)
    (hweak : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → ∃ i, R i = S i)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    Real.rpow (∫ x, Real.rpow (finiteFunctionMaximal G f x) p) (1 / p) ≤
      (maximalDimensionConstant d + 3) * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x, Real.rpow |f x| p) (1 / p) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hK : 0 ≤ maximalDimensionConstant d := by
    unfold maximalDimensionConstant
    exact sq_nonneg _
  have hC : 0 ≤ (maximalDimensionConstant d + 3) * (p / (p - 1)) ^ (m - 1) :=
    mul_nonneg (add_nonneg hK (by norm_num))
      (pow_nonneg (div_nonneg hp0.le (sub_pos.mpr hp).le) _)
  have hA : 0 ≤ ∫ x, Real.rpow (finiteFunctionMaximal G f x) p :=
    integral_nonneg (fun x => Real.rpow_nonneg (finiteFunctionMaximal_nonneg G f x) p)
  have hB : 0 ≤ ∫ x, Real.rpow |f x| p :=
    integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) p)
  exact root_bound_of_power_bound hA hB hC hp0
    (finite_weaker_grid_maximal_integral hm hd D G hG hweak f p hp hf)

/-- Extended integral form for the countable limiting step. -/
theorem finite_weaker_grid_maximal_lintegral
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : ↑G ⊆ gridRectangles D)
    (hweak : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → ∃ i, R i = S i)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    (∫⁻ x, (ENNReal.ofReal (finiteFunctionMaximal G f x)) ^ p) ≤
      (ENNReal.ofReal ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1))) ^ p *
          ∫⁻ x, (ENNReal.ofReal |f x|) ^ p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpow : Integrable (fun x => Real.rpow |f x| p) volume := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le, Real.rpow_eq_pow] using
      hf.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
  have hout := integrable_rpow_finiteFunctionMaximal G f p hp0
  have houtE : (∫⁻ x, (ENNReal.ofReal (finiteFunctionMaximal G f x)) ^ p) =
      ENNReal.ofReal (∫ x, Real.rpow (finiteFunctionMaximal G f x) p) := by
    simp_rw [ENNReal.ofReal_rpow_of_nonneg (finiteFunctionMaximal_nonneg G f _) hp0.le]
    exact (ofReal_integral_eq_lintegral_ofReal hout
      (Filter.Eventually.of_forall (fun x =>
        Real.rpow_nonneg (finiteFunctionMaximal_nonneg G f x) p))).symm
  have hinE : (∫⁻ x, (ENNReal.ofReal |f x|) ^ p) =
      ENNReal.ofReal (∫ x, Real.rpow |f x| p) := by
    simp_rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
    exact (ofReal_integral_eq_lintegral_ofReal hpow
      (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (abs_nonneg _) p))).symm
  have hK : 0 ≤ maximalDimensionConstant d := by
    unfold maximalDimensionConstant
    exact sq_nonneg _
  have hC : 0 ≤ (maximalDimensionConstant d + 3) * (p / (p - 1)) ^ (m - 1) :=
    mul_nonneg (add_nonneg hK (by norm_num))
      (pow_nonneg (div_nonneg hp0.le (sub_pos.mpr hp).le) _)
  rw [houtE, hinE, ENNReal.ofReal_rpow_of_nonneg hC hp0.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hC p)]
  exact ENNReal.ofReal_le_ofReal (finite_weaker_grid_maximal_integral hm hd D G hG hweak f p hp hf)

end ReyZygmund

