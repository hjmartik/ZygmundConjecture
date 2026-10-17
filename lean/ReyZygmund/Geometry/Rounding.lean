import ReyZygmund.MathlibOnly.Definitions
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Prescribed dyadic side lengths

A positive side length `s` is rounded to the integer `ceil (logb 2 s) + 2`.
The rounding bins have an open lower endpoint and a closed upper endpoint.
The order assertions apply to positive inputs.
-/

open ReyZygmund.MathlibOnly (rounding)

namespace ReyZygmund.Geometry

/-- Exact bins, including every dyadic endpoint. -/
theorem rounding_eq_iff {s : ℝ} (hs : 0 < s) (k : ℤ) :
    rounding s = k ↔ (2 : ℝ) ^ (k - 3) < s ∧ s ≤ (2 : ℝ) ^ (k - 2) := by
  unfold rounding
  rw [show (⌈Real.logb 2 s⌉ + 2 = k) ↔ ⌈Real.logb 2 s⌉ = k - 2 by omega,
    Int.ceil_eq_iff]
  rw [show ((k - 2 : ℤ) : ℝ) - 1 = ((k - 3 : ℤ) : ℝ) by push_cast; ring,
    Real.lt_logb_iff_rpow_lt (by norm_num) hs,
    Real.logb_le_iff_le_rpow (by norm_num) hs]
  simp only [Real.rpow_intCast]

/-- The prescribed side is at least four and strictly less than eight times
the original positive side. -/
theorem rounding_bounds {s : ℝ} (hs : 0 < s) :
    4 * s ≤ (2 : ℝ) ^ rounding s ∧ (2 : ℝ) ^ rounding s < 8 * s := by
  have h := (rounding_eq_iff hs (rounding s)).mp rfl
  have h2 : (2 : ℝ) ^ (rounding s - 2) = (2 : ℝ) ^ rounding s / 4 := by
    rw [zpow_sub₀ (by norm_num)]
    norm_num
  have h3 : (2 : ℝ) ^ (rounding s - 3) = (2 : ℝ) ^ rounding s / 8 := by
    rw [zpow_sub₀ (by norm_num)]
    norm_num
  rw [h2, h3] at h
  constructor <;> linarith

theorem rounding_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    rounding s ≤ rounding t := by
  have h := Int.ceil_mono
    (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hs hst)
  unfold rounding
  omega

/-- Strictly ordered rounded scales force strict order of the original sides.
Equal rounded scales do not supply such an order. -/
theorem lt_of_rounding_lt {s t : ℝ} (ht : 0 < t)
    (h : rounding s < rounding t) : s < t := by
  by_contra hst
  have := rounding_mono ht (le_of_not_gt hst)
  omega

end ReyZygmund.Geometry
