import ReyZygmund.MathlibOnly.FamilyBridge
import ReyZygmund.Main.Overlap

/-! # Sparse incomparable moments and exponential overlap -/

namespace ReyZygmund.MathlibOnly

theorem incomparable_overlap : IncomparableOverlap := by
  obtain ⟨C, c, hC, hc, h⟩ := Main.incomparable_overlap_theorem
  refine ⟨C, c, hC, hc, ?_⟩
  intro m d hm hd D G hG hinc eta heta heta1 hs hv
  rw [gridRectangles_eq] at hG
  exact h m d hm hd (fun i => (D i).toDyadicGrid) G hG hinc eta heta heta1
    ((sparse_iff_challenge eta G).mp hs) hv

end ReyZygmund.MathlibOnly
