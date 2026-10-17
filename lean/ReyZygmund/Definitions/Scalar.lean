import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Scalar energy in the weighted square-function estimates

The function `scalarPsi` is the energy used in `Weighted/Scalar.lean`.
-/

namespace ReyZygmund

/-- The scalar function `Ψ_p(a,b) = a² / b^(2-p)` in the weighted square estimate. -/
noncomputable def scalarPsi (p a b : ℝ) : ℝ :=
  a ^ (2 : ℕ) / Real.rpow b (2 - p)

end ReyZygmund
