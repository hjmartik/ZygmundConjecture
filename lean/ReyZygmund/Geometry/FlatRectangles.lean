import ReyZygmund.Geometry.Flatten
import ReyZygmund.Geometry.ProductSteps
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Rectangles and integrals under coordinate flattening -/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- The axis-parallel box obtained by listing the product corners. -/
noncomputable def flatProductBox (Q : ∀ i, Box (Fin (d i))) : Box (Fin (∑ i, d i)) where
  lower := flattenCoordinates d (fun i => (Q i).lower)
  upper := flattenCoordinates d (fun i => (Q i).upper)
  lower_lt_upper j := by
    obtain ⟨⟨i, k⟩, rfl⟩ := (finSigmaFinEquiv (n := d)).surjective j
    simpa only [flattenCoordinates_apply] using (Q i).lower_lt_upper k

theorem mem_flatProductBox (Q : ∀ i, Box (Fin (d i))) (x : ProductPoint d) :
    flattenCoordinates d x ∈ flatProductBox Q ↔ x ∈ productBox Q := by
  rw [mem_productBox]
  change (∀ j, flattenCoordinates d (fun i => (Q i).lower) j < flattenCoordinates d x j ∧
    flattenCoordinates d x j ≤ flattenCoordinates d (fun i => (Q i).upper) j) ↔ _
  constructor
  · intro h i k
    simpa only [flattenCoordinates_apply, Set.mem_Ioc] using h (finSigmaFinEquiv ⟨i, k⟩)
  · intro h j
    obtain ⟨⟨i, k⟩, rfl⟩ := (finSigmaFinEquiv (n := d)).surjective j
    simpa only [flattenCoordinates_apply, Set.mem_Ioc] using h i k

theorem preimage_flatProductBox (Q : ∀ i, Box (Fin (d i))) :
    flattenCoordinates d ⁻¹' (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) =
      productBox Q := by
  ext x
  exact mem_flatProductBox Q x

theorem volume_flatProductBox (Q : ∀ i, Box (Fin (d i))) :
    volume (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) = volume (productBox Q) := by
  rw [← (volume_preserving_flattenCoordinates d).map_eq,
    MeasurableEquiv.map_apply, preimage_flatProductBox]

/-- Set integrals agree under the measure-preserving coordinates.
This identity itself is total; analytic uses retain their input integrability. -/
theorem integral_flatProductBox (Q : ∀ i, Box (Fin (d i)))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) :
    (∫ x in productBox Q, f (flattenCoordinates d x)) =
      ∫ y in (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)), f y := by
  have h := (volume_preserving_flattenCoordinates d).restrict_preimage
    (flatProductBox Q).measurableSet_coe
  rw [preimage_flatProductBox] at h
  exact h.integral_comp' f

theorem average_flatProductBox (Q : ∀ i, Box (Fin (d i)))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) :
    (∫ x in productBox Q, f (flattenCoordinates d x)) / volume.real (productBox Q) =
      (∫ y in (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)), f y) /
        volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) := by
  rw [integral_flatProductBox]
  congr 1
  exact congrArg ENNReal.toReal (volume_flatProductBox Q).symm

theorem memLp_comp_flattenCoordinates
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ≥0∞)
    (hf : MemLp f p volume) :
    MemLp (fun x => f (flattenCoordinates d x)) p volume :=
  hf.comp_measurePreserving (volume_preserving_flattenCoordinates d)

theorem eLpNorm_comp_flattenCoordinates
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ≥0∞)
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (fun x => f (flattenCoordinates d x)) p volume = eLpNorm f p volume :=
  eLpNorm_comp_measurePreserving hf (volume_preserving_flattenCoordinates d)

end ReyZygmund.Geometry
