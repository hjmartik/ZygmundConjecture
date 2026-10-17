import ReyZygmund.MathlibOnly.Definitions
import ReyZygmund.Overlap.Countable

/-! # Shadow and overlap in Euclidean coordinates

The product-coordinate rectangles and the flattened boxes describe the same
sets. Their unions and sums of indicators therefore agree pointwise.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.MathlibOnly.Proof.Estimates

variable {m : ℕ} {d : Fin m → ℕ}

/-- The union of the rectangles is the same after flattening coordinates. -/
theorem shadow_eq (G : Set (∀ i, Box (Fin (d i)))) : shadow G = Overlap.shadow G := by
  ext x
  simp only [shadow, Overlap.shadow, Geometry.rectangle_eq_flatProductBox,
    Set.mem_iUnion, Subtype.exists]

/-- Flattening coordinates preserves the sum of rectangle indicators. -/
theorem overlap_eq (G : Set (∀ i, Box (Fin (d i)))) : overlap G = Overlap.overlap G := by
  funext x
  simp only [overlap, Overlap.overlap, Geometry.rectangle_eq_flatProductBox]

end ReyZygmund.MathlibOnly.Proof.Estimates
