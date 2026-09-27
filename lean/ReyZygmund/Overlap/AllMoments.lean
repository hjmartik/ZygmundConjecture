import ReyZygmund.Overlap.SmallMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Completing the real moment range without losing the second-moment constant

The sparse-duality bound retains `(q - 1)^k`. At q = 2 this is one,
so finite-measure Holder fills the range down to one with the same constant.
-/

open MeasureTheory
open scoped ENNReal

namespace ReyZygmund.Overlap

/-- Exact high-moment growth supplies every real order at least one, with the
coefficient required for the endpoint-to-overlap exponential bound. -/
theorem all_moments_of_high_moments {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (H : X → ℝ)
    (hm : Measurable H) (hn : ∀ x, 0 ≤ H x) (k : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hhigh : ∀ q : ℝ, 2 ≤ q →
      (∫⁻ x, (ENNReal.ofReal (H x)) ^ q ∂μ) ≤
        (ENNReal.ofReal (C * (q - 1) ^ k)) ^ q * μ Set.univ)
    (q : ℝ) (hq : 1 ≤ q) :
    (∫⁻ x, (ENNReal.ofReal (H x)) ^ q ∂μ) ≤
      (ENNReal.ofReal (C * q ^ k)) ^ q * μ Set.univ := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  by_cases hq2 : 2 ≤ q
  · apply (hhigh q hq2).trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.rpow_le_rpow _ hq0.le
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith : 0 ≤ q - 1) (by linarith : q - 1 ≤ q) k) hC
  · have hsecond : (∫⁻ x, (ENNReal.ofReal (H x)) ^ (2 : ℝ) ∂μ) ≤
        (ENNReal.ofReal C) ^ (2 : ℝ) * μ Set.univ := by
      simpa only [show (2 : ℝ) - 1 = 1 by norm_num, one_pow, mul_one] using
        hhigh 2 (le_refl _)
    apply (small_moment_of_second_moment μ H hm hn C hsecond q hq0
      (le_of_not_ge hq2)).trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.rpow_le_rpow _ hq0.le
    apply ENNReal.ofReal_le_ofReal
    exact le_mul_of_one_le_right hC (one_le_pow₀ hq)

end ReyZygmund.Overlap
