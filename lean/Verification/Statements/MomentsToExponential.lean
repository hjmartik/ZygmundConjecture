import ReyZygmund.Overlap.MomentsToExponential

/-! The uniform measure-theoretic moment-to-exponential proposition. -/

open MeasureTheory
open scoped ENNReal

universe u

namespace ReyZygmundVerification

def momentsToExponentialContract : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (C : ℝ), 0 < C →
    ∃ c B : ℝ, 0 < c ∧ 0 < B ∧
      ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
        (H : α → ℝ), Measurable H → (∀ x, 0 ≤ H x) →
        (∀ q : ℝ, 2 ≤ q →
          (∫⁻ x, (ENNReal.ofReal (H x)) ^ q ∂μ) ≤
            (ENNReal.ofReal (C * q ^ k)) ^ q * μ Set.univ) →
        (∫⁻ x, ENNReal.ofReal
          (Real.exp (c * Real.rpow (H x) (1 / (k : ℝ))) - 1) ∂μ) ≤
          ENNReal.ofReal B * μ Set.univ

end ReyZygmundVerification
