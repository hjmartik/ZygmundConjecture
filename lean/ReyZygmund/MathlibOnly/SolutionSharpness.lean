import ReyZygmund.MathlibOnly.FamilyBridge
import ReyZygmund.Main.Sharpness

/-! # One sharpness sequence for every larger exponential power -/

namespace ReyZygmund.MathlibOnly

theorem phi_sparse_sharpness : PhiSparseSharpness := by
  intro n hn d hd D eta heta heta1
  obtain ⟨G, hG, hlim⟩ := Main.phi_sparse_sharpness_theorem n hn d hd
    (fun i => (D i).toDyadicGrid) eta heta heta1
  refine ⟨G, ?_, hlim⟩
  intro N hN
  obtain ⟨hfamily, hinc, hs, hv⟩ := hG N hN
  rw [← phiRectangles_eq] at hfamily
  exact ⟨hfamily, hinc, (sparse_iff_challenge _ _).mpr hs, hv⟩

end ReyZygmund.MathlibOnly
