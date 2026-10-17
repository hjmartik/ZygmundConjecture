import ReyZygmund.MathlibOnly.Proof.Definitions
import ReyZygmund.MathlibOnly.Proof.OperatorBridge
import ReyZygmund.Geometry.ProductContainment

/-!
# Containment and weak incomparability

These identities relate containment of rectangles to the coordinatewise box
order, and express weak incomparability as containment leaving a factor unchanged.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.MathlibOnly.Proof.Estimates

theorem rectangle_subset_iff {m : ℕ} {d : Fin m → ℕ}
    (R S : ∀ i, Box (Fin (d i))) :
    rectangle R ⊆ rectangle S ↔ ∀ i, R i ≤ S i := by
  rw [Geometry.rectangle_eq_flatProductBox, Geometry.rectangle_eq_flatProductBox]
  have h : (Geometry.flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ⊆
      Geometry.flatProductBox S ↔ Geometry.productRectangle R ⊆ Geometry.productRectangle S := by
    constructor
    · intro h x hx
      exact (Geometry.mem_flatProductBox S x).mp
        (h ((Geometry.mem_flatProductBox R x).mpr hx))
    · intro h x hx
      obtain ⟨y, rfl⟩ := (Geometry.flattenCoordinates d).surjective x
      exact (Geometry.mem_flatProductBox S y).mpr
        (h ((Geometry.mem_flatProductBox R y).mp hx))
  exact h.trans (Geometry.productRectangle_subset_iff R S)

/-- Weak incomparability is equivalent to the condition
that containment leaves a factor unchanged. -/
theorem weaklyIncomparable_iff_equalFactor {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i)))) :
    WeaklyIncomparable G ↔ HasEqualFactorOnContainment G := by
  rw [Geometry.weaklyIncomparable_iff_equal_factor]
  constructor
  · intro h R hR S hS hRS
    exact h R hR S hS ((rectangle_subset_iff R S).mp hRS)
  · intro h R hR S hS hRS
    exact h R hR S hS ((rectangle_subset_iff R S).mpr hRS)

end ReyZygmund.MathlibOnly.Proof.Estimates
