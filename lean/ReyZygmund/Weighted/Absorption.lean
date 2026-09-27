import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The scalar absorption step

The two terms are separated before any cancellation. The remaining real-power
inequality is resolved with an explicit constant uniform for `1 < p ≤ 3/2`.
No norm, maximal operator, or integrability hypothesis is encoded here.
-/

namespace ReyZygmund.Weighted

private theorem absorb_mixed_term (θ A X Y : ℝ)
    (hθ : 0 < θ) (hA : 0 ≤ A) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : X ≤ A * Y ^ θ * X ^ (1 - θ)) :
    X ≤ A ^ θ⁻¹ * Y := by
  by_cases hzero : X = 0
  · rw [hzero]
    exact mul_nonneg (Real.rpow_nonneg hA _) hY
  have hXpos : 0 < X := lt_of_le_of_ne hX (Ne.symm hzero)
  have hsplit : X ^ θ * X ^ (1 - θ) = X := by
    rw [← Real.rpow_add hXpos, show θ + (1 - θ) = 1 by ring, Real.rpow_one]
  have hcancel : X ^ θ ≤ A * Y ^ θ := by
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hXpos (1 - θ))).mp
    rw [mul_comm (X ^ (1 - θ)) (X ^ θ), hsplit,
      mul_comm (X ^ (1 - θ)) (A * Y ^ θ)]
    exact h
  have hpower := Real.rpow_le_rpow (Real.rpow_nonneg hX θ) hcancel
    (inv_nonneg.mpr hθ.le)
  simpa only [Real.mul_rpow hA (Real.rpow_nonneg hY θ),
    Real.rpow_rpow_inv hX hθ.ne', Real.rpow_rpow_inv hY hθ.ne'] using hpower

private theorem half_weight_sq (s : ℝ) (hs : 0 < s) (k : ℕ) :
    (s ^ (-((k : ℕ) : ℝ) / 2)) ^ 2 = (1 / s) ^ k := by
  calc
    _ = s ^ ((-(k : ℝ) / 2) * (2 : ℕ)) :=
      (Real.rpow_mul_natCast hs.le _ 2).symm
    _ = s ^ (-(k : ℝ)) := by congr 1; ring
    _ = (s ^ (k : ℝ))⁻¹ := Real.rpow_neg hs.le _
    _ = (1 / s) ^ k := by rw [Real.rpow_natCast, one_div, inv_pow]

/-- The scalar absorption estimate has a constant uniform in `p`. The expressions `m -
2` and `m - 1` use natural-number subtraction. -/
theorem weighted_absorption
    (m : ℕ) (hm : 2 ≤ m)
    (p C X Y : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 / 2 : ℝ))
    (hC : 1 ≤ C) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : X ≤ C * (p / (p - 1)) ^ (m - 2) * Y +
      C * Real.rpow (p - 1) (-((m - 1 : ℕ) : ℝ) / 2) *
        Real.rpow Y (p / 2) * Real.rpow X (1 - p / 2)) :
    X ≤ (2 * C) ^ 2 * (p / (p - 1)) ^ (m - 1) * Y := by
  let q : ℝ := p / (p - 1)
  let w : ℝ := (p - 1) ^ (-((m - 1 : ℕ) : ℝ) / 2)
  have hs : 0 < p - 1 := sub_pos.mpr hp
  have hs1 : p - 1 ≤ 1 := by linarith
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hq1 : 1 ≤ q := (one_le_div₀ hs).mpr (by linarith)
  have hq0 : 0 ≤ q := zero_le_one.trans hq1
  have hw1 : 1 ≤ w := by
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs hs1
    have hk : (0 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hw0 : 0 ≤ w := zero_le_one.trans hw1
  have hmstep : m - 1 = (m - 2) + 1 := by omega
  have hqpow : q ^ (m - 2) ≤ q ^ (m - 1) := by
    rw [hmstep]
    exact pow_le_pow_right₀ hq1 (Nat.le_succ _)
  change X ≤ (2 * C) ^ 2 * q ^ (m - 1) * Y
  change X ≤ C * q ^ (m - 2) * Y + C * w * Y ^ (p / 2) * X ^ (1 - p / 2) at h
  by_cases heasy : X ≤ 2 * (C * q ^ (m - 2) * Y)
  · have hcoef : 2 * C ≤ (2 * C) ^ 2 := by nlinarith
    calc
      X ≤ 2 * (C * q ^ (m - 2) * Y) := heasy
      _ = (2 * C) * q ^ (m - 2) * Y := by ring
      _ ≤ (2 * C) ^ 2 * q ^ (m - 1) * Y :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hcoef hqpow (pow_nonneg hq0 _) (sq_nonneg _)) hY
  · have hθ : 0 < p / 2 := by linarith
    have hmixed : X ≤ (2 * C * w) * Y ^ (p / 2) * X ^ (1 - p / 2) := by
      calc
        X ≤ 2 * (C * w * Y ^ (p / 2) * X ^ (1 - p / 2)) := by
          linarith [lt_of_not_ge heasy]
        _ = _ := by ring
    have hresolved := absorb_mixed_term (p / 2) (2 * C * w) X Y hθ
      (mul_nonneg (mul_nonneg (by norm_num) hC0) hw0) hX hY hmixed
    have hbase : 1 ≤ 2 * C * w := by
      have htwo : 1 ≤ 2 * C := by linarith
      exact one_le_mul_of_one_le_of_one_le htwo hw1
    have hinv : (p / 2)⁻¹ ≤ 2 := by
      simpa only [one_div] using
        (div_le_iff₀ hθ).mpr (show (1 : ℝ) ≤ 2 * (p / 2) by linarith)
    have hpower : (2 * C * w) ^ (p / 2)⁻¹ ≤ (2 * C * w) ^ 2 := by
      simpa only [Real.rpow_two] using
        Real.rpow_le_rpow_of_exponent_le hbase hinv
    have hbaseCompare : 1 / (p - 1) ≤ q :=
      div_le_div_of_nonneg_right hp.le hs.le
    have hweight : w ^ 2 ≤ q ^ (m - 1) := by
      dsimp only [w]
      rw [half_weight_sq (p - 1) hs (m - 1)]
      exact pow_le_pow_left₀ (one_div_nonneg.mpr hs.le) hbaseCompare _
    calc
      X ≤ (2 * C * w) ^ (p / 2)⁻¹ * Y := hresolved
      _ ≤ (2 * C * w) ^ 2 * Y := mul_le_mul_of_nonneg_right hpower hY
      _ = ((2 * C) ^ 2 * w ^ 2) * Y := by rw [mul_pow]
      _ ≤ ((2 * C) ^ 2 * q ^ (m - 1)) * Y :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hweight (sq_nonneg _)) hY

end ReyZygmund.Weighted
