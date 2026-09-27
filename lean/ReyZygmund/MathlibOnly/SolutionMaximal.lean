import ReyZygmund.MathlibOnly.FamilyBridge
import ReyZygmund.Main.Maximal

/-! # The incomparable maximal estimate in the independent specification -/

namespace ReyZygmund.MathlibOnly

/-- Arbitrary source-defined grids, arbitrary incomparable families and every
real `p > 1`, with no sparsity or finite-shadow premise. -/
theorem incomparable_maximal : IncomparableMaximal := by
  obtain ⟨C, hC, h⟩ := Main.incomparable_maximal_theorem
  refine ⟨C, hC, ?_⟩
  intro m d hm hd D G hG hinc p hp f hf
  rw [gridRectangles_eq] at hG
  exact h m d hm hd (fun i => (D i).toDyadicGrid) G hG hinc p hp f hf

end ReyZygmund.MathlibOnly
