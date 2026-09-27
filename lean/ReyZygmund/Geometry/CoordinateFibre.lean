import ReyZygmund.Geometry.ProductSteps
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-! # Coordinate operators on a fixed-coordinate slice

After fixing coordinate `j`, the remaining dimensions are indexed by
`j.succAbove`. Coordinate insertion identifies the slices used by averages and
differences. Support and constancy on the smallest cubes pass to these slices. The
identities prepare the lower-dimensional application of the maximal–square
estimate.


-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

variable {n : ℕ} {d : Fin (n + 1) → ℕ}

/-- Inserting a fixed coordinate is a measurable map between the
Euclidean product spaces, including the empty remaining product. -/
theorem measurable_coordinateFibre_insertNth
    (j : Fin (n + 1)) (t : Fin (d j) → ℝ) :
    Measurable (fun y : ProductPoint (fun i => d (j.succAbove i)) =>
      j.insertNth (α := fun i => Fin (d i) → ℝ) t y) := by
  exact (MeasurableEquiv.piFinSuccAbove (fun i => Fin (d i) → ℝ) j).symm.measurable.comp
    (measurable_const.prodMk measurable_id)

/-- The two averages have exactly the same supported integral and volume.
No integrability assumption is needed for this identity by congruence. -/
theorem coordinateAverage_insertNth
    (j : Fin (n + 1)) (t : Fin (d j) → ℝ) (i : Fin n)
    (Q : Box (Fin (d (j.succAbove i)))) (f : ProductPoint d → ℝ)
    (y : ProductPoint (fun k => d (j.succAbove k))) :
    coordinateAverage i Q (fun z => f (j.insertNth t z)) y =
      coordinateAverage (j.succAbove i) Q f (j.insertNth t y) := by
  simp only [coordinateAverage, Fin.insertNth_apply_succAbove, Fin.insertNth_update]

/-- Child averages minus the parent average commute with
inserting an unselected coordinate. No cutoff convention is changed. -/
theorem coordinateDifference_insertNth
    (j : Fin (n + 1)) (t : Fin (d j) → ℝ) (i : Fin n)
    (Q : Box (Fin (d (j.succAbove i)))) (f : ProductPoint d → ℝ)
    (y : ProductPoint (fun k => d (j.succAbove k))) :
    coordinateDifference i Q (fun z => f (j.insertNth t z)) y =
      coordinateDifference (j.succAbove i) Q f (j.insertNth t y) := by
  simp only [coordinateDifference, Pi.sub_apply, Finset.sum_apply, coordinateAverage_insertNth]

/-- A slice through a point of the top rectangle is constant on the remaining smallest
product cubes. Support and positivity are not required. -/
theorem productLeafConstant_coordinateFibre
    (I : ∀ i, Box (Fin (d i))) (N : Fin (n + 1) → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (j : Fin (n + 1)) (t : Fin (d j) → ℝ) (ht : t ∈ I j) :
    ProductLeafConstant (fun i => I (j.succAbove i)) (fun i => N (j.succAbove i))
      (fun y => f (j.insertNth t y)) := by
  obtain ⟨R, hR, htR⟩ := level_isPartition (I j) (N j) t ht
  intro P hP x hx y hy
  change f (j.insertNth t x) = f (j.insertNth t y)
  have hP' : j.insertNth R P ∈ productLeaves I N := by
    apply Fintype.mem_piFinset.mpr
    refine j.forall_iff_succAbove.mpr ⟨?_, ?_⟩
    · simpa only [Fin.insertNth_apply_same, leaves, Prepartition.mem_boxes] using hR
    · intro i
      simpa only [Fin.insertNth_apply_succAbove] using Fintype.mem_piFinset.mp hP i
  have hmem (z : ProductPoint (fun i => d (j.succAbove i))) (hz : z ∈ productBox P) :
      j.insertNth t z ∈ productBox (j.insertNth R P) := by
    apply (mem_productBox _ _).mpr
    refine j.forall_iff_succAbove.mpr ⟨?_, ?_⟩
    · simpa only [Fin.insertNth_apply_same] using htR
    · intro i
      simpa only [Fin.insertNth_apply_succAbove] using (mem_productBox P z).mp hz i
  exact hf _ hP' _ (hmem x hx) _ (hmem y hy)

/-- Support restricts to each slice, also when the fixed coordinate is outside the top
cube. Constancy on the smallest cubes is not required. -/
theorem coordinateFibre_eq_zero_of_notMem_root
    (I : ∀ i, Box (Fin (d i))) (f : ProductPoint d → ℝ)
    (hs : ∀ x, x ∉ productBox I → f x = 0)
    (j : Fin (n + 1)) (t : Fin (d j) → ℝ)
    (y : ProductPoint (fun i => d (j.succAbove i)))
    (hy : y ∉ productBox (fun i => I (j.succAbove i))) :
    f (j.insertNth t y) = 0 := by
  apply hs
  intro hx
  apply hy
  apply (mem_productBox _ y).mpr
  intro i
  simpa only [Fin.insertNth_apply_succAbove] using
    (mem_productBox I _).mp hx (j.succAbove i)

end ReyZygmund.Geometry
