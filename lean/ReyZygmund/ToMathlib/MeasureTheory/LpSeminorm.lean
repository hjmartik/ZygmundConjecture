import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Norm of an almost-everywhere finite nonnegative function -/

open scoped ENNReal

namespace MeasureTheory

/-- An almost-everywhere finite nonnegative function has the same norm as
its real-valued representative, including when the norm is infinite. -/
theorem eLpNorm_eq_toReal {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ≥0∞} (p : ℝ≥0∞)
    (hf : ∀ᵐ x ∂μ, f x < ∞) :
    eLpNorm f p μ = eLpNorm (fun x => (f x).toReal) p μ := by
  calc
    eLpNorm f p μ = eLpNorm (ENNReal.ofReal ∘ fun x => (f x).toReal) p μ := by
      apply eLpNorm_congr_ae
      filter_upwards [hf] with x hx
      exact (ENNReal.ofReal_toReal hx.ne).symm
    _ = eLpNorm (fun x => (f x).toReal) p μ :=
      eLpNorm_ofReal _ (.of_forall fun _ => ENNReal.toReal_nonneg)

end MeasureTheory
