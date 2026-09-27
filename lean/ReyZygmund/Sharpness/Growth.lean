import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The scalar growth and retention choice in Section 7

The natural power records the mass of the maximum-overlap set. The power
inside the exponential is a real power. Its exponent is strictly greater
than one, so it dominates the linear logarithm of the geometric decay.
The retention scale is chosen independently of the family index.
-/

open Filter
open scoped Topology

namespace ReyZygmund.Sharpness

/-- The precise scalar lower bound in the final sharpness calculation tends
to infinity. The subtraction `N - 1` and the outer power are natural. -/
theorem tendsto_retained_exp_lower_bound
    (r : ℕ) (hr : 0 < r) (δ c β : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc : 0 < c) (hβ : 1 / (r : ℝ) < β) :
    Tendsto (fun N : ℕ => δ ^ (r * (N - 1)) *
      (Real.exp (c * Real.rpow (N : ℝ) ((r : ℝ) * β)) - 1)) atTop atTop := by
  let α : ℝ := (r : ℝ) * β
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hα : 1 < α := by
    dsimp [α]
    simpa only [mul_comm] using (div_lt_iff₀ hrR).mp hβ
  have hpower : Tendsto (fun N : ℕ => Real.rpow (N : ℝ) (α - 1)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < α - 1)).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop,
      (1 - (r : ℝ) * Real.log δ) / c ≤ Real.rpow (N : ℝ) (α - 1) :=
    hpower.eventually_ge_atTop _
  refine tendsto_atTop_mono' atTop (f₁ := fun N : ℕ => (N : ℝ)) ?_
    tendsto_natCast_atTop_atTop
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with N hNlarge hN
  have hN0 : 0 < (N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hlinear : 1 - (r : ℝ) * Real.log δ ≤ c * Real.rpow (N : ℝ) (α - 1) := by
    have h := (div_le_iff₀ hc).mp hNlarge
    nlinarith
  have hsplit : Real.rpow (N : ℝ) (α - 1) * (N : ℝ) = Real.rpow (N : ℝ) α := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add_one hN0.ne', sub_add_cancel]
  have hdom := mul_le_mul_of_nonneg_right hlinear hN0.le
  rw [mul_assoc, hsplit] at hdom
  have hexponent : (N : ℝ) ≤ ((r * N : ℕ) : ℝ) * Real.log δ +
      c * Real.rpow (N : ℝ) α := by
    rw [Nat.cast_mul]
    nlinarith [hdom]
  have hexp : Real.exp (N : ℝ) ≤
      δ ^ (r * N) * Real.exp (c * Real.rpow (N : ℝ) α) := by
    calc
      Real.exp (N : ℝ) ≤ Real.exp (((r * N : ℕ) : ℝ) * Real.log δ +
          c * Real.rpow (N : ℝ) α) := Real.exp_le_exp.mpr hexponent
      _ = δ ^ (r * N) * Real.exp (c * Real.rpow (N : ℝ) α) := by
        rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hδ0]
  have hdecay : δ ^ (r * N) ≤ 1 := pow_le_one₀ hδ0.le hδ1.le
  have hdecay_le : δ ^ (r * N) ≤ δ ^ (r * (N - 1)) :=
    pow_le_pow_of_le_one hδ0.le hδ1.le (Nat.mul_le_mul_left r (Nat.sub_le N 1))
  have hexp0 : 0 ≤ Real.exp (c * Real.rpow (N : ℝ) α) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr
      (mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg N) α)))
  calc
    (N : ℝ) ≤ Real.exp (N : ℝ) - 1 := by
      linarith [Real.add_one_le_exp (N : ℝ)]
    _ ≤ δ ^ (r * N) * (Real.exp (c * Real.rpow (N : ℝ) α) - 1) := by
      nlinarith [hexp, hdecay]
    _ ≤ δ ^ (r * (N - 1)) * (Real.exp (c * Real.rpow (N : ℝ) α) - 1) :=
      mul_le_mul_of_nonneg_right hdecay_le hexp0

/-- A single retention scale works independently of the family index. The
paper's strict positivity premise on `η` is retained in the public type. -/
theorem exists_retention_scale (r : ℕ) (hr : 0 < r) (η : ℝ)
    (_hη0 : 0 < η) (hη1 : η < 1) :
    ∃ s : ℕ, 1 ≤ s ∧ η ≤ (1 - (2 : ℝ) ^ (-(s : ℤ))) ^ r := by
  have hhalf : Tendsto (fun s : ℕ => ((2 : ℝ)⁻¹) ^ s) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlimit : Tendsto (fun s : ℕ => (1 - ((2 : ℝ)⁻¹) ^ s) ^ r) atTop (𝓝 1) := by
    simpa only [sub_zero, one_pow] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hhalf).pow r
  have hevent : ∀ᶠ s : ℕ in atTop, η < (1 - ((2 : ℝ)⁻¹) ^ s) ^ r :=
    hlimit.eventually (Ioi_mem_nhds hη1)
  obtain ⟨s, hs, hret⟩ := ((eventually_ge_atTop r).and hevent).exists
  refine ⟨s, (Nat.succ_le_iff.mpr hr).trans hs, ?_⟩
  simpa only [zpow_neg, zpow_natCast, inv_pow] using hret.le

end ReyZygmund.Sharpness
