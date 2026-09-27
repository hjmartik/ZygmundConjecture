import ReyZygmund.MathlibOnly.OperatorBridge
import ReyZygmund.Main.Endpoints

/-! # The prescribed rounded endpoint in the independent specification -/

namespace ReyZygmund.MathlibOnly

/-- The whole rounded scale image in every indicated shifted grid, not a
single-valued replacement for that image. -/
theorem rounded_endpoint : RoundedEndpoint := by
  intro n totalDim hn
  obtain ⟨C, hC, h⟩ := Main.rounded_endpoint_theorem n totalDim hn
  refine ⟨C, hC, ?_⟩
  intro d hd hdim phi hphi tau f hf lam hlam
  rw [roundedRectangles_eq, maximal_eq_endpoint _ f hf]
  exact h d hd hdim phi hphi tau f hf lam hlam

end ReyZygmund.MathlibOnly
