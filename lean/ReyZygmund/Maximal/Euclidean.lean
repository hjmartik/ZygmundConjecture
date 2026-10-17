import ReyZygmund.Maximal.Countable
import ReyZygmund.Geometry.FlatRectangles

/-! # The maximal function in ordinary Euclidean coordinates

The operator below uses the flattened rectangles and their Lebesgue averages.
Its equality with the block-coordinate operator is pointwise.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

open ReyZygmund.MathlibOnly (CubeGrid gridRectangles)

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- The supremum of supported averages over the Euclidean rectangles. -/
noncomputable def euclideanFamilyMaximal
    (G : Set (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (x : Fin (∑ i, d i) → ℝ) : ℝ≥0∞ :=
  ⨆ Q : G, ENNReal.ofReal
    ((flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)).indicator
      (fun _ => (∫ y in (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)), |f y|) /
        volume.real (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ))) x)

theorem euclideanFamilyMaximal_flatten
    (G : Set (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (x : ProductPoint d) :
    euclideanFamilyMaximal G f (flattenCoordinates d x) =
      familyMaximal G (fun y => f (flattenCoordinates d y)) x := by
  unfold euclideanFamilyMaximal familyMaximal
  congr 1
  funext Q
  congr 1
  rw [Set.indicator_apply, Set.indicator_apply,
    show flattenCoordinates d x ∈ (flatProductBox Q.1 : Set _) ↔ x ∈ productRectangle Q.1 from
      mem_flatProductBox Q.1 x,
    ← average_flatProductBox Q.1 (fun y => |f y|)]

theorem measurable_euclideanFamilyMaximal
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G.Countable)
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) : Measurable (euclideanFamilyMaximal G f) := by
  have := hG.to_subtype
  exact Measurable.iSup (fun Q : G =>
    ((measurable_const : Measurable (fun _ : Fin (∑ i, d i) → ℝ =>
      (∫ y in (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)), |f y|) /
        volume.real (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)))).indicator
          (flatProductBox Q.1).measurableSet_coe).ennreal_ofReal)

end ReyZygmund
