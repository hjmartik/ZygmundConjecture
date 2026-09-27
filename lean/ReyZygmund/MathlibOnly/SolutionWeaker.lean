import ReyZygmund.MathlibOnly.FamilyBridge
import ReyZygmund.Main.Overlap

/-! # All three conclusions under the weaker containment condition -/

namespace ReyZygmund.MathlibOnly

theorem weaker_containment : WeakerContainment := by
  obtain ⟨C, c, hC, hc, h⟩ := Main.weaker_containment_theorem
  refine ⟨C, c, hC, hc, ?_⟩
  intro m d hm hd D G hG hgeom
  rw [gridRectangles_eq] at hG
  obtain ⟨hmax, hoverlap⟩ := h m d hm hd (fun i => (D i).toDyadicGrid) G hG hgeom
  refine ⟨hmax, ?_⟩
  intro eta heta heta1 hs hv
  exact hoverlap eta heta heta1 ((sparse_iff_challenge eta G).mp hs) hv

end ReyZygmund.MathlibOnly
