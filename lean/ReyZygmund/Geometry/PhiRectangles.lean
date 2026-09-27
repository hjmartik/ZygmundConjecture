import ReyZygmund.Geometry.FlatRectangles
import Mathlib.Data.Fin.Tuple.Basic

/-! # The continuous Phi family

Every block is an axis-parallel cube at an arbitrary position. Its side
length is prescribed by a positive first-side tuple and the positive side
function in the last block. No grid, regularity, or estimate is part of
this definition. Monotonicity is a hypothesis of the later theorems.
-/

open BoxIntegral

namespace ReyZygmund.Geometry

/-- The Phi rectangle family, at every position. -/
def continuousPhiRectangles {n : ℕ} (d : Fin (n + 1) → ℕ)
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) :
    Set (∀ i, Box (Fin (d i))) :=
  {R | ∃ s : Fin n → Set.Ioi (0 : ℝ),
    ∀ i a, (R i).upper a - (R i).lower a =
      (Fin.snoc (fun j => (s j).1) (phi s).1 : Fin (n + 1) → ℝ) i}

end ReyZygmund.Geometry
