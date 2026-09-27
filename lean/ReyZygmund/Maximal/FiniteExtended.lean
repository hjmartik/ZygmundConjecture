import ReyZygmund.Maximal.FiniteGrid

/-! # Extended power-integral form of the finite grid estimate

This is the form used by monotone convergence. Both real power integrals
are integrable before conversion to nonnegative extended integrals.
-/

open BoxIntegral MeasureTheory
open scoped Classical ENNReal

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

theorem finite_grid_maximal_lintegral
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : ↑G ⊆ gridRectangles D)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
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
  exact ENNReal.ofReal_le_ofReal (finite_grid_maximal_integral hm hd D G hG hinc f p hp hf)

end ReyZygmund
