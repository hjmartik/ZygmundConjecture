import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Independent statement reconstructed by the correspondence reviewer from the paper.
It deliberately expands the scalar quotient and imports no project proof or definition.
-/

namespace ReyZygmundVerification

def scalarEstimateContract : Prop :=
  ∀ (p a h b η : ℝ),
    1 < p → p ≤ 2 → 0 < b → 0 < b + η →
    (p - 1) / (3 - p) *
        (h ^ (2 : ℕ) / Real.rpow (max b (b + η)) (2 - p)) ≤
      (a + h) ^ (2 : ℕ) / Real.rpow (b + η) (2 - p) -
        a ^ (2 : ℕ) / Real.rpow b (2 - p) -
        2 * a * h / Real.rpow b (2 - p) +
        (2 - p) * a ^ (2 : ℕ) * η / Real.rpow b (3 - p)

end ReyZygmundVerification
