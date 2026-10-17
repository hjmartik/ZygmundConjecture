import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! # Restoring the constant term in an exponential integral -/

open scoped ENNReal

namespace MeasureTheory

/-- Restore the constant term in an exponential integral by adding the
measurable constant one. -/
theorem lintegral_exp_le_add_one {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) (v : α → ℝ) (hv : ∀ x, 0 ≤ v x)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (∫⁻ x in s, ENNReal.ofReal (Real.exp (v x)) - 1 ∂μ) ≤
      ENNReal.ofReal C * μ s) :
    (∫⁻ x in s, ENNReal.ofReal (Real.exp (v x)) ∂μ) ≤
      ENNReal.ofReal (C + 1) * μ s := by
  have hpoint (x) : ENNReal.ofReal (Real.exp (v x)) =
      (ENNReal.ofReal (Real.exp (v x)) - 1) + 1 := by
    apply (tsub_add_cancel_of_le _).symm
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr (hv x))
  calc
    (∫⁻ x in s, ENNReal.ofReal (Real.exp (v x)) ∂μ) =
        (∫⁻ x in s, (ENNReal.ofReal (Real.exp (v x)) - 1) + 1 ∂μ) :=
      lintegral_congr hpoint
    _ = (∫⁻ x in s, ENNReal.ofReal (Real.exp (v x)) - 1 ∂μ) + μ s := by
      rw [lintegral_add_right _ measurable_const]
      simp
    _ ≤ ENNReal.ofReal C * μ s + μ s := add_le_add h le_rfl
    _ = ENNReal.ofReal (C + 1) * μ s := by
      rw [ENNReal.ofReal_add hC zero_le_one, ENNReal.ofReal_one, add_mul, one_mul]

end MeasureTheory
