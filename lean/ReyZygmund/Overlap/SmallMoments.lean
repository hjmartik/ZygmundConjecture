import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Small real moments from the second moment

This is the finite-measure Hölder step in the endpoint-to-overlap argument.
There is no division by the total mass, so the zero-measure case is included.
-/

open MeasureTheory
open scoped ENNReal

namespace ReyZygmund.Overlap

/-- A normalized second-moment bound retains the same coefficient at every
positive real exponent at most two. -/
theorem small_moment_of_second_moment {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (H : X → ℝ)
    (hm : Measurable H) (hn : ∀ x, 0 ≤ H x) (C : ℝ)
    (hsecond : (∫⁻ x, (ENNReal.ofReal (H x)) ^ (2 : ℝ) ∂μ) ≤
      (ENNReal.ofReal C) ^ (2 : ℝ) * μ Set.univ)
    (q : ℝ) (hq : 0 < q) (hq2 : q ≤ 2) :
    (∫⁻ x, (ENNReal.ofReal (H x)) ^ q ∂μ) ≤
      (ENNReal.ofReal C) ^ q * μ Set.univ := by
  have hexp : 0 ≤ 1 / q - 1 / 2 := by
    have hi : (1 : ℝ) / 2 ≤ 1 / q := one_div_le_one_div_of_le hq hq2
    linarith
  have hnorm := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ (μ := μ) hq hq2
    hm.aestronglyMeasurable
  simp only [eLpNorm'_eq_lintegral_enorm] at hnorm
  simp_rw [Real.enorm_of_nonneg (hn _)] at hnorm
  have hroot := ENNReal.rpow_le_rpow hsecond (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h : (∫⁻ x, (ENNReal.ofReal (H x)) ^ q ∂μ) ^ (1 / q) ≤
      ENNReal.ofReal C * (μ Set.univ) ^ (1 / q) := by
    apply hnorm.trans
    calc
      _ ≤ ((ENNReal.ofReal C) ^ (2 : ℝ) * μ Set.univ) ^ (1 / 2 : ℝ) *
          (μ Set.univ) ^ (1 / q - 1 / 2) := mul_le_mul_left hroot _
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
          ENNReal.rpow_one, mul_assoc,
          ← ENNReal.rpow_add_of_nonneg (1 / 2) (1 / q - 1 / 2)
            (by norm_num) hexp,
          show (1 / 2 : ℝ) + (1 / q - 1 / 2) = 1 / q by ring]
  have hp := ENNReal.rpow_le_rpow h hq.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul,
    one_div_mul_cancel hq.ne', ENNReal.rpow_one] at hp
  exact hp

end ReyZygmund.Overlap
