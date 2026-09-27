import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! Statements for the quantitative tail and exponential bounds. Only Mathlib is
imported, not the tail proofs. The moment-growth order `k` is one greater than the
endpoint logarithmic order.
-/

open MeasureTheory
open scoped ENNReal

namespace ReyZygmundVerification

noncomputable def exponentialTailExactContract : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (Y : X → ℝ), Measurable Y → (∀ x, 0 ≤ Y x) →
    (∀ t : ℝ, 1 ≤ t →
      mu {x | t < Y x} ≤ ENNReal.ofReal (Real.exp (-t)) * mu Set.univ) →
    (∫⁻ x, ENNReal.ofReal (Real.exp ((1 / 2 : ℝ) * Y x)) ∂mu) ≤ 3 * mu Set.univ

noncomputable def polynomialMomentsExponentialExactContract : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (H : X → ℝ), Measurable H → (∀ x, 0 ≤ H x) →
    ∀ (k : ℕ), 1 ≤ k → ∀ (C : ℝ), 0 < C →
    (∀ q : ℝ, 1 ≤ q →
      (∫⁻ x, ENNReal.ofReal (Real.rpow (H x) q) ∂mu) ≤
        ENNReal.ofReal (Real.rpow (C * q ^ k) q) * mu Set.univ) →
    (∫⁻ x, ENNReal.ofReal (Real.exp
      ((1 / 2 : ℝ) * Real.rpow (H x / (Real.exp 1 * C)) (1 / (k : ℝ)))) ∂mu) ≤
        3 * mu Set.univ

end ReyZygmundVerification
