import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Scalar function in the quantitative remainder inequality

The denominator uses a real power. Its required positivity is a hypothesis of the
theorem in `Weighted/Scalar.lean`.

-/

namespace ReyZygmund

/-- The scalar function `Ψ_p(a,b) = a² / b^(2-p)` in the weighted square estimate. -/
noncomputable def scalarPsi (p a b : ℝ) : ℝ :=
  a ^ (2 : ℕ) / Real.rpow b (2 - p)

end ReyZygmund
