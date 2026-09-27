import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The scalar logarithmic-exponential Young estimate

The constant is fixed before the two nonnegative inputs. A single term of the
exponential series gives the polynomial bound needed in the large-input case;
no asymptotic growth estimate is assumed.
-/

namespace ReyZygmund.Scalar

private theorem polynomial_le_exp_above (k : ℕ) (α A t : ℝ)
    (hα : 0 < α) (ht : 0 ≤ t)
    (hthreshold : A * ((k + 1).factorial : ℝ) / α ^ (k + 1) ≤ t) :
    A * t ^ k ≤ Real.exp (α * t) := by
  have hf : 0 < ((k + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (k + 1)
  have hpower : 0 < α ^ (k + 1) := pow_pos hα _
  have hlin : A * ((k + 1).factorial : ℝ) ≤ t * α ^ (k + 1) :=
    (div_le_iff₀ hpower).mp hthreshold
  calc
    A * t ^ k ≤ (α * t) ^ (k + 1) / ((k + 1).factorial : ℝ) := by
      apply (le_div_iff₀ hf).mpr
      calc
        A * t ^ k * ((k + 1).factorial : ℝ) =
            (A * ((k + 1).factorial : ℝ)) * t ^ k := by ring
        _ ≤ (t * α ^ (k + 1)) * t ^ k :=
          mul_le_mul_of_nonneg_right hlin (pow_nonneg ht _)
        _ = (α * t) ^ (k + 1) := by
          rw [mul_pow, pow_succ t]
          ring
    _ ≤ Real.exp (α * t) :=
      Real.pow_div_factorial_le_exp (α * t) (mul_nonneg hα.le ht) (k + 1)

/-- The paper's scalar estimate, including zero inputs and the exact inverse
factor. The logarithmic power is natural and the power of `b` is real. -/
theorem orlicz_young
    (k : ℕ) (hk : 1 ≤ k) (c C1 C2 : ℝ)
    (hc : 0 < c) (hC1 : 0 < C1) (hC2 : 0 < C2) :
    ∃ C3 : ℝ, 0 < C3 ∧ ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      C1 * a * b ≤ C3 * a * (Real.log (Real.exp 1 + a)) ^ k +
        (2 * C2)⁻¹ * Real.exp (c * Real.rpow b (1 / (k : ℝ))) := by
  let α : ℝ := c / 2
  have hα : 0 < α := by dsimp [α]; linarith
  let T : ℝ := (2 * C1 * C2) * ((k + 1).factorial : ℝ) / α ^ (k + 1)
  let M : ℝ := 1 + max (1 / α) T
  have hMα : 1 / α ≤ M := by
    dsimp [M]
    linarith [le_max_left (1 / α) T]
  have hMT : T ≤ M := by
    dsimp [M]
    linarith [le_max_right (1 / α) T]
  have hM : 0 < M := (one_div_pos.mpr hα).trans_le hMα
  have hαM : 1 ≤ α * M := by
    have h := (div_le_iff₀ hα).mp hMα
    simpa only [mul_comm] using h
  refine ⟨C1 * M ^ k, mul_pos hC1 (pow_pos hM _), ?_⟩
  intro a b ha hb
  let t : ℝ := Real.rpow b (1 / (k : ℝ))
  let ℓ : ℝ := Real.log (Real.exp 1 + a)
  have ht : 0 ≤ t := Real.rpow_nonneg hb _
  have hk0 : k ≠ 0 := ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk)
  have htk : t ^ k = b := by
    dsimp [t]
    simpa only [one_div] using Real.rpow_inv_natCast_pow hb hk0
  have harg : 0 < Real.exp 1 + a := add_pos_of_pos_of_nonneg (Real.exp_pos _) ha
  have hℓ : 1 ≤ ℓ :=
    (Real.le_log_iff_exp_le harg).mpr (le_add_of_nonneg_right ha)
  have hℓ0 : 0 ≤ ℓ := zero_le_one.trans hℓ
  have hfirst : 0 ≤ (C1 * M ^ k) * a * ℓ ^ k :=
    mul_nonneg (mul_nonneg (mul_nonneg hC1.le (pow_nonneg hM.le _)) ha)
      (pow_nonneg hℓ0 _)
  have hsecond : 0 ≤ (2 * C2)⁻¹ * Real.exp (c * t) := by positivity
  change C1 * a * b ≤ (C1 * M ^ k) * a * ℓ ^ k +
    (2 * C2)⁻¹ * Real.exp (c * t)
  by_cases hsmall : t ≤ M * ℓ
  · have hbpower : b ≤ M ^ k * ℓ ^ k := by
      calc
        b = t ^ k := htk.symm
        _ ≤ (M * ℓ) ^ k := pow_le_pow_left₀ ht hsmall k
        _ = M ^ k * ℓ ^ k := mul_pow M ℓ k
    have hmain : C1 * a * b ≤ (C1 * M ^ k) * a * ℓ ^ k := by
      calc
        C1 * a * b ≤ C1 * a * (M ^ k * ℓ ^ k) :=
          mul_le_mul_of_nonneg_left hbpower (mul_nonneg hC1.le ha)
        _ = (C1 * M ^ k) * a * ℓ ^ k := by ring
    exact hmain.trans (le_add_of_nonneg_right hsecond)
  · have hlarge : M * ℓ < t := lt_of_not_ge hsmall
    have hMt : M ≤ t := by
      calc
        M = M * 1 := (mul_one M).symm
        _ ≤ M * ℓ := mul_le_mul_of_nonneg_left hℓ hM.le
        _ ≤ t := hlarge.le
    have hℓbound : ℓ ≤ α * t := by
      calc
        ℓ = 1 * ℓ := (one_mul ℓ).symm
        _ ≤ (α * M) * ℓ := mul_le_mul_of_nonneg_right hαM hℓ0
        _ = α * (M * ℓ) := by ring
        _ ≤ α * t := mul_le_mul_of_nonneg_left hlarge.le hα.le
    have haexp : a ≤ Real.exp (α * t) := by
      calc
        a ≤ Real.exp 1 + a := le_add_of_nonneg_left (Real.exp_pos _).le
        _ = Real.exp ℓ := (Real.exp_log harg).symm
        _ ≤ Real.exp (α * t) := Real.exp_le_exp.mpr hℓbound
    have hpoly : (2 * C1 * C2) * b ≤ Real.exp (α * t) := by
      rw [← htk]
      exact polynomial_le_exp_above k α (2 * C1 * C2) t hα ht (hMT.trans hMt)
    have hden : 0 < 2 * C2 := mul_pos (by norm_num) hC2
    have hcoef : C1 * b ≤ (2 * C2)⁻¹ * Real.exp (α * t) := by
      calc
        C1 * b ≤ Real.exp (α * t) / (2 * C2) := by
          apply (le_div_iff₀ hden).mpr
          calc
            (C1 * b) * (2 * C2) = (2 * C1 * C2) * b := by ring
            _ ≤ Real.exp (α * t) := hpoly
        _ = (2 * C2)⁻¹ * Real.exp (α * t) := by rw [div_eq_mul_inv, mul_comm]
    have hsum : α * t + α * t = c * t := by dsimp [α]; ring
    have hmain : C1 * a * b ≤ (2 * C2)⁻¹ * Real.exp (c * t) := by
      calc
        C1 * a * b = (C1 * b) * a := by ring
        _ ≤ ((2 * C2)⁻¹ * Real.exp (α * t)) * Real.exp (α * t) :=
          mul_le_mul hcoef haexp ha
            (mul_nonneg (inv_nonneg.mpr hden.le) (Real.exp_pos _).le)
        _ = (2 * C2)⁻¹ * Real.exp (c * t) := by
          rw [mul_assoc, ← Real.exp_add, hsum]
    exact hmain.trans (le_add_of_nonneg_left hfirst)

end ReyZygmund.Scalar
