import ReyZygmund.MathlibOnly.GridBridge
import ReyZygmund.MathlibOnly.OperatorBridge

/-! # Exact transport of the independently defined dyadic families -/

open BoxIntegral

namespace ReyZygmund.MathlibOnly

theorem gridRectangles_eq {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, CubeGrid (d i)) :
    gridRectangles D =
      ReyZygmundVerification.Challenges.gridRectangles (fun i => (D i).toDyadicGrid) := by
  ext R
  simp only [gridRectangles, ReyZygmundVerification.Challenges.gridRectangles,
    Set.mem_ofPred_eq, CubeGrid.mem_toDyadicGrid_all]

theorem phiRectangles_eq {n : ℕ} {d : Fin (n + 1) → ℕ}
    (D : ∀ i, CubeGrid (d i)) (Phi : (Fin n → ℤ) → ℤ) :
    phiRectangles D Phi =
      ReyZygmundVerification.Challenges.phiGridRectangles
        (fun i => (D i).toDyadicGrid) Phi := by
  simp only [phiRectangles, ReyZygmundVerification.Challenges.phiGridRectangles,
    CubeGrid.toDyadicGrid_cubes, neg_neg]

end ReyZygmund.MathlibOnly
