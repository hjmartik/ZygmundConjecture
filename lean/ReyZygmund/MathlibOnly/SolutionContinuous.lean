import ReyZygmund.MathlibOnly.OperatorBridge
import ReyZygmund.Continuous.Endpoint

/-! # The continuous endpoint in the independent specification -/

namespace ReyZygmund.MathlibOnly

/-- The full arbitrary-position continuous endpoint, with the maximal operator
defined using nonnegative integrals in the Mathlib-only specification. -/
theorem continuous_endpoint : ContinuousEndpoint := by
  intro n totalDim hn
  obtain ⟨C, hC, h⟩ := Continuous.continuous_endpoint_theorem n totalDim hn
  refine ⟨C, hC, ?_⟩
  intro d hd hdim phi hphi f hf lam hlam
  rw [continuousRectangles_eq, maximal_eq_endpoint _ f hf]
  exact h d hd hdim phi hphi f hf lam hlam

end ReyZygmund.MathlibOnly
