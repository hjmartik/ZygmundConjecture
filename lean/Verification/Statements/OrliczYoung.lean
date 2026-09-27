import ReyZygmund.Scalar.OrliczYoung

/-! Explicit expected proposition for the scalar logarithmic-exponential estimate. -/

namespace ReyZygmundVerification

def orliczYoungContract : Prop :=
  ∀ (k : ℕ), 1 ≤ k →
  ∀ (c C1 C2 : ℝ), 0 < c → 0 < C1 → 0 < C2 →
    ∃ C3 : ℝ, 0 < C3 ∧ ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      C1 * a * b ≤ C3 * a * (Real.log (Real.exp 1 + a)) ^ k +
        (2 * C2)⁻¹ * Real.exp (c * Real.rpow b (1 / (k : ℝ)))

end ReyZygmundVerification
