import ReyZygmund.Weighted.Absorption

/-! Explicit expected proposition for the quantitative scalar absorption step. -/

namespace ReyZygmundVerification

def weightedAbsorptionContract : Prop :=
  ∀ (m : ℕ), 2 ≤ m →
  ∀ (p C X Y : ℝ), 1 < p → p ≤ (3 / 2 : ℝ) →
    1 ≤ C → 0 ≤ X → 0 ≤ Y →
    X ≤ C * (p / (p - 1)) ^ (m - 2) * Y +
      C * Real.rpow (p - 1) (-((m - 1 : ℕ) : ℝ) / 2) *
        Real.rpow Y (p / 2) * Real.rpow X (1 - p / 2) →
    X ≤ (2 * C) ^ 2 * (p / (p - 1)) ^ (m - 1) * Y

end ReyZygmundVerification
