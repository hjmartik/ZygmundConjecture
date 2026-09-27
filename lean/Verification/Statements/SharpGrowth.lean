import ReyZygmund.Sharpness.Growth

/-! Expected propositions for the scalar Section 7 limits. -/

open Filter

namespace ReyZygmundVerification

def sharpExponentialGrowthContract : Prop :=
  ∀ (r : ℕ), 0 < r → ∀ (δ c β : ℝ), 0 < δ → δ < 1 → 0 < c →
    1 / (r : ℝ) < β →
    Tendsto (fun N : ℕ => δ ^ (r * (N - 1)) *
      (Real.exp (c * Real.rpow (N : ℝ) ((r : ℝ) * β)) - 1)) atTop atTop

def sharpRetentionScaleContract : Prop :=
  ∀ (r : ℕ), 0 < r → ∀ (η : ℝ), 0 < η → η < 1 →
    ∃ s : ℕ, 1 ≤ s ∧ η ≤ (1 - (2 : ℝ) ^ (-(s : ℤ))) ^ r

end ReyZygmundVerification
