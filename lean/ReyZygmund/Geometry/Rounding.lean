import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Prescribed dyadic side lengths

The paper rounds a positive side length `s` to the integer
`ceil (logb 2 s) + 2`. These identities retain the open lower bin endpoint
and the closed upper endpoint. All order assertions are on positive inputs;
no monotonicity assertion is made for the total logarithm on nonpositive inputs.
-/

namespace ReyZygmund.Geometry

/-- The integer logarithmic scale of the prescribed dyadic covering cube. -/
noncomputable def roundedScale (s : ℝ) : ℤ := ⌈Real.logb 2 s⌉ + 2

/-- Exact bins, including every dyadic endpoint. -/
theorem roundedScale_eq_iff {s : ℝ} (hs : 0 < s) (k : ℤ) :
    roundedScale s = k ↔ (2 : ℝ) ^ (k - 3) < s ∧ s ≤ (2 : ℝ) ^ (k - 2) := by
  unfold roundedScale
  rw [show (⌈Real.logb 2 s⌉ + 2 = k) ↔ ⌈Real.logb 2 s⌉ = k - 2 by omega,
    Int.ceil_eq_iff]
  rw [show ((k - 2 : ℤ) : ℝ) - 1 = ((k - 3 : ℤ) : ℝ) by push_cast; ring,
    Real.lt_logb_iff_rpow_lt (by norm_num) hs,
    Real.logb_le_iff_le_rpow (by norm_num) hs]
  simp only [Real.rpow_intCast]

/-- The prescribed side is at least four and strictly less than eight times
the original positive side. -/
theorem roundedScale_bounds {s : ℝ} (hs : 0 < s) :
    4 * s ≤ (2 : ℝ) ^ roundedScale s ∧ (2 : ℝ) ^ roundedScale s < 8 * s := by
  have h := (roundedScale_eq_iff hs (roundedScale s)).mp rfl
  have h2 : (2 : ℝ) ^ (roundedScale s - 2) = (2 : ℝ) ^ roundedScale s / 4 := by
    rw [zpow_sub₀ (by norm_num)]
    norm_num
  have h3 : (2 : ℝ) ^ (roundedScale s - 3) = (2 : ℝ) ^ roundedScale s / 8 := by
    rw [zpow_sub₀ (by norm_num)]
    norm_num
  rw [h2, h3] at h
  constructor <;> linarith

theorem roundedScale_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    roundedScale s ≤ roundedScale t := by
  have h := Int.ceil_mono
    (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hs hst)
  unfold roundedScale
  omega

/-- Strictly ordered rounded scales force strict order of the original sides.
Equal rounded scales do not supply such an order. -/
theorem lt_of_roundedScale_lt {s t : ℝ} (ht : 0 < t)
    (h : roundedScale s < roundedScale t) : s < t := by
  by_contra hst
  have := roundedScale_mono ht (le_of_not_gt hst)
  omega

end ReyZygmund.Geometry
