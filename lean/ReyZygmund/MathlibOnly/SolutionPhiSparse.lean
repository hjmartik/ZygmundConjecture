import ReyZygmund.MathlibOnly.FamilyBridge
import ReyZygmund.Main.PhiSparse

/-! # Sparse prescribed-scale overlap without incomparability -/

namespace ReyZygmund.MathlibOnly

theorem phi_sparse_overlap : PhiSparseOverlap := by
  intro n totalDim hn eta heta heta1
  obtain ⟨c, C, hc, hC, h⟩ := Main.phi_sparse_overlap_theorem n totalDim hn eta heta heta1
  refine ⟨c, C, hc, hC, ?_⟩
  intro d hd hdim D Phi hPhi G hG hs hv
  rw [phiRectangles_eq] at hG
  exact h d hd hdim (fun i => (D i).toDyadicGrid) Phi hPhi G hG
    ((sparse_iff_challenge eta G).mp hs) hv

end ReyZygmund.MathlibOnly
