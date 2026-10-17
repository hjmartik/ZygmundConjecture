import ReyZygmund.MathlibOnly.SupportingStatements
import ReyZygmund.MathlibOnly.Proof.OperatorBridge
import ReyZygmund.Continuous.DyadicEndpoint

/-! # The dyadic Zygmund conjecture

Extend the integer scale relation by taking floors of base-two logarithms.
The continuous endpoint estimate then applies to a family containing every
dyadic rectangle. Local integrability identifies the two forms of its averages.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace ReyZygmund.MathlibOnly

/-- The dyadic endpoint follows from the continuous estimate for the extended relation. -/
theorem dyadic_zygmund_conjecture : DyadicZygmundConjecture := by
  intro n totalDim hn
  obtain ⟨C, hC, hbound⟩ := Continuous.dyadic_phi_endpoint_theorem n totalDim hn
  refine ⟨C, hC, ?_⟩
  intro d hd hdim D Phi hPhi f hf lam hlam
  rw [Proof.maximal_eq_euclidean_of_locallyIntegrable _ f hf]
  simpa only [show n + 1 - 2 = n - 1 by omega] using
    hbound d hd hdim D Phi hPhi f hf lam hlam

end ReyZygmund.MathlibOnly
