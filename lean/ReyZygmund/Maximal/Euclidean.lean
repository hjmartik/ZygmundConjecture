import ReyZygmund.Maximal.Global
import ReyZygmund.Geometry.FlatRectangles

/-! # The maximal estimate in ordinary Euclidean coordinates

The operator below uses the flattened rectangles and their Lebesgue
averages. Its equality with the block-coordinate operator is pointwise,
before any norm or almost-everywhere representative is used.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

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
    show flattenCoordinates d x ∈ (flatProductBox Q.1 : Set _) ↔ x ∈ productBox Q.1 from
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

/-- Almost-everywhere finiteness of the Euclidean supremum. -/
theorem euclidean_grid_maximal_ae_finite
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → R = S)
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∀ᵐ x ∂volume, euclideanFamilyMaximal G f x < ∞ := by
  have hfin := grid_family_maximal_ae_finite hm hd D G hG
    (fun R hR S hS hRS => hinc R hR S hS ((productBox_subset_iff R S).mpr hRS))
      (fun y => f (flattenCoordinates d y)) p hp (memLp_comp_flattenCoordinates f _ hf)
  have hmap := (volume_preserving_flattenCoordinates d).map_eq
  rw [← hmap]
  apply (ae_map_iff (flattenCoordinates d).measurable.aemeasurable
    ((measurable_euclideanFamilyMaximal G ((countable_gridRectangles D).mono hG) f)
      measurableSet_Iio)).mpr
  simpa only [euclideanFamilyMaximal_flatten, Set.mem_Iio] using hfin

/-- The main norm estimate in ordinary Euclidean coordinates, with the same
dimension-only constant and no finite-family or bounded-input restriction. -/
theorem euclidean_grid_maximal_eLpNorm
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → R = S)
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (fun x => (euclideanFamilyMaximal G f x).toReal) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1)) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hmeas := (measurable_euclideanFamilyMaximal G
    ((countable_gridRectangles D).mono hG) f).ennreal_toReal
  rw [← eLpNorm_comp_flattenCoordinates _ _ hmeas.aestronglyMeasurable]
  simp_rw [euclideanFamilyMaximal_flatten]
  exact (incomparable_grid_maximal_eLpNorm hm hd D G hG hinc
    (fun y => f (flattenCoordinates d y)) p hp (memLp_comp_flattenCoordinates f _ hf)).trans_eq
      (congrArg (ENNReal.ofReal ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1)) * ·)
        (eLpNorm_comp_flattenCoordinates f _ hf.aestronglyMeasurable))

end ReyZygmund
