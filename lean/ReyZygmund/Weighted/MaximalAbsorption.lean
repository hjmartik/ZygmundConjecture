import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Absorption with the intermediate exponent

The represented maximal estimate first separates the easy term. In the
remaining case it cancels a power of the maximal norm and raises to `2 / p`.
The intermediate exponent `(m - 1) / p` is retained until the final comparison.
-/

namespace ReyZygmund.Weighted

/-- Cancel the mixed norm power and raise to `2 / p`.
The resulting exponent of `p'` is exactly `k / p`.
The zero norm is handled before cancellation. -/
theorem mixed_term_bound
    (k : ℕ) (p A X Y : ℝ) (hp : 1 < p)
    (hA : 0 ≤ A) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : X ≤ A * Real.rpow (p / (p - 1)) ((k : ℝ) / 2) *
      Real.rpow Y (p / 2) * Real.rpow X (1 - p / 2)) :
    X ≤ Real.rpow A (2 / p) * Real.rpow (p / (p - 1)) ((k : ℝ) / p) * Y := by
  let q := p / (p - 1)
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hq : 0 ≤ q := div_nonneg hp0.le (sub_pos.mpr hp).le
  have hqPower : 0 ≤ Real.rpow q ((k : ℝ) / 2) := Real.rpow_nonneg hq _
  change X ≤ A * Real.rpow q ((k : ℝ) / 2) *
    Real.rpow Y (p / 2) * Real.rpow X (1 - p / 2) at h
  change X ≤ Real.rpow A (2 / p) * Real.rpow q ((k : ℝ) / p) * Y
  by_cases hzero : X = 0
  · rw [hzero]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hq _)) hY
  have hXpos : 0 < X := lt_of_le_of_ne hX (Ne.symm hzero)
  have hsplit : Real.rpow X (p / 2) * Real.rpow X (1 - p / 2) = X := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hXpos, show p / 2 + (1 - p / 2) = 1 by ring, Real.rpow_one]
  have hcancel : Real.rpow X (p / 2) ≤
      (A * Real.rpow q ((k : ℝ) / 2)) * Real.rpow Y (p / 2) := by
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hXpos (1 - p / 2))).mp
    simp only [Real.rpow_eq_pow] at hsplit h ⊢
    rw [mul_comm (X ^ (1 - p / 2)) (X ^ (p / 2)), hsplit,
      mul_comm (X ^ (1 - p / 2)) ((A * q ^ ((k : ℝ) / 2)) * Y ^ (p / 2))]
    exact h
  have hpower := Real.rpow_le_rpow (Real.rpow_nonneg hX _) hcancel
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp0.le)
  have hexp : (p / 2) * (2 / p) = 1 := by field_simp [ne_of_gt hp0]
  have hXroot : Real.rpow (Real.rpow X (p / 2)) (2 / p) = X := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul hX, hexp, Real.rpow_one]
  have hYroot : Real.rpow (Real.rpow Y (p / 2)) (2 / p) = Y := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul hY, hexp, Real.rpow_one]
  have hqroot : Real.rpow (Real.rpow q ((k : ℝ) / 2)) (2 / p) =
      Real.rpow q ((k : ℝ) / p) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul hq]
    congr 1
    ring
  calc
    X = Real.rpow (Real.rpow X (p / 2)) (2 / p) := hXroot.symm
    _ ≤ Real.rpow ((A * Real.rpow q ((k : ℝ) / 2)) * Real.rpow Y (p / 2))
        (2 / p) := hpower
    _ = Real.rpow A (2 / p) * Real.rpow q ((k : ℝ) / p) * Y := by
      simp only [Real.rpow_eq_pow] at hqPower hqroot hYroot ⊢
      rw [Real.mul_rpow (mul_nonneg hA hqPower) (Real.rpow_nonneg hY _),
        Real.mul_rpow hA hqPower, hqroot, hYroot]

/-- The two-case absorption argument, with a dimension-only output coefficient.
In the hard case the proof first obtains `(2 * C)^2 * (p')^((m - 1) / p) * Y`;
only then does it replace the intermediate exponent by `m - 1`. -/
theorem weighted_absorption_conjugate
    (m : ℕ) (hm : 2 ≤ m)
    (p C X Y : ℝ) (hp : 1 < p) (_hp3 : p ≤ (3 / 2 : ℝ))
    (hC : 1 ≤ C) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : X ≤ C * (p / (p - 1)) ^ (m - 2) * Y +
      C * Real.rpow (p / (p - 1)) (((m - 1 : ℕ) : ℝ) / 2) *
        Real.rpow Y (p / 2) * Real.rpow X (1 - p / 2)) :
    X ≤ (2 * C) ^ 2 * (p / (p - 1)) ^ (m - 1) * Y := by
  let q := p / (p - 1)
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hs : 0 < p - 1 := sub_pos.mpr hp
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hq1 : 1 ≤ q := (one_le_div₀ hs).mpr (by linarith)
  have hq0 : 0 ≤ q := zero_le_one.trans hq1
  have hmstep : m - 1 = (m - 2) + 1 := by omega
  have hqpow : q ^ (m - 2) ≤ q ^ (m - 1) := by
    rw [hmstep]
    exact pow_le_pow_right₀ hq1 (Nat.le_succ _)
  change X ≤ (2 * C) ^ 2 * q ^ (m - 1) * Y
  change X ≤ C * q ^ (m - 2) * Y +
    C * Real.rpow q (((m - 1 : ℕ) : ℝ) / 2) *
      Real.rpow Y (p / 2) * Real.rpow X (1 - p / 2) at h
  by_cases heasy : X ≤ 2 * (C * q ^ (m - 2) * Y)
  · have hcoefficient : 2 * C ≤ (2 * C) ^ 2 := by nlinarith
    calc
      X ≤ 2 * (C * q ^ (m - 2) * Y) := heasy
      _ = (2 * C) * q ^ (m - 2) * Y := by ring
      _ ≤ (2 * C) ^ 2 * q ^ (m - 1) * Y :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hcoefficient hqpow (pow_nonneg hq0 _) (sq_nonneg _)) hY
  · have hmixed : X ≤ (2 * C) * Real.rpow q (((m - 1 : ℕ) : ℝ) / 2) *
        Real.rpow Y (p / 2) * Real.rpow X (1 - p / 2) := by
      calc
        X ≤ 2 * (C * Real.rpow q (((m - 1 : ℕ) : ℝ) / 2) *
            Real.rpow Y (p / 2) * Real.rpow X (1 - p / 2)) := by
          linarith [lt_of_not_ge heasy]
        _ = _ := by ring
    have hresolved := mixed_term_bound (m - 1) p (2 * C) X Y hp
      (mul_nonneg (by norm_num) hC0) hX hY hmixed
    change X ≤ Real.rpow (2 * C) (2 / p) *
      Real.rpow q (((m - 1 : ℕ) : ℝ) / p) * Y at hresolved
    have hbase : 1 ≤ 2 * C := by linarith
    have hpower : Real.rpow (2 * C) (2 / p) ≤ (2 * C) ^ 2 := by
      have hexponent : 2 / p ≤ (2 : ℝ) := (div_le_iff₀ hp0).mpr (by linarith)
      simpa only [Real.rpow_eq_pow, Real.rpow_two] using
        Real.rpow_le_rpow_of_exponent_le hbase hexponent
    have hintermediate : X ≤ (2 * C) ^ 2 *
        Real.rpow q (((m - 1 : ℕ) : ℝ) / p) * Y :=
      hresolved.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg hq0 _)) hY)
    have hexponent : ((m - 1 : ℕ) : ℝ) / p ≤ ((m - 1 : ℕ) : ℝ) := by
      apply (div_le_iff₀ hp0).mpr
      calc
        ((m - 1 : ℕ) : ℝ) = ((m - 1 : ℕ) : ℝ) * 1 := by ring
        _ ≤ ((m - 1 : ℕ) : ℝ) * p :=
          mul_le_mul_of_nonneg_left hp.le (Nat.cast_nonneg _)
    have hfinal : Real.rpow q (((m - 1 : ℕ) : ℝ) / p) ≤ q ^ (m - 1) := by
      simpa only [Real.rpow_eq_pow, Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_le hq1 hexponent
    exact hintermediate.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfinal (sq_nonneg _)) hY)

end ReyZygmund.Weighted
