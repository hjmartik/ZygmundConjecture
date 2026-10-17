import ReyZygmund.Geometry.SlicedOverlap
import ReyZygmund.Overlap.FiniteIdentification

/-! # Finite slices, shadows and overlap

The finite slice is the image of exactly those rectangles whose last cube
contains the slicing point. Incomparability makes this projection injective,
allowing the overlap sum to be reindexed.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

open ReyZygmund.MathlibOnly (CubeGrid gridRectangles initialProjection sliceFamily)

namespace ReyZygmund.Geometry

open Overlap

variable {n : ℕ} {d : Fin (n + 1) → ℕ}

/-- The finite version of `sliceFamily`. -/
noncomputable def finiteSlice (G : Finset (∀ i, Box (Fin (d i))))
    (t : Fin (d (Fin.last n)) → ℝ) :
    Finset (∀ i : Fin n, Box (Fin (d i.castSucc))) :=
  (G.filter (fun R => t ∈ R (Fin.last n))).image initialProjection

theorem coe_finiteSlice (G : Finset (∀ i, Box (Fin (d i))))
    (t : Fin (d (Fin.last n)) → ℝ) :
    (↑(finiteSlice G t) : Set (∀ i : Fin n, Box (Fin (d i.castSucc)))) =
      sliceFamily (↑G) t := by
  ext P
  simp only [finiteSlice, Finset.mem_coe, Finset.mem_image, Finset.mem_filter,
    sliceFamily, Set.mem_image, Set.mem_ofPred_eq]

theorem mem_flatProductBox_splitLast_symm (R : ∀ i, Box (Fin (d i)))
    (y : Fin (∑ i : Fin n, d i.castSucc) → ℝ) (t : Fin (d (Fin.last n)) → ℝ) :
    (splitLastCoordinates d).symm (y, t) ∈ flatProductBox R ↔
      y ∈ flatProductBox (initialProjection R) ∧ t ∈ R (Fin.last n) := by
  simpa only [MeasurableEquiv.apply_symm_apply, Set.mem_prod, Box.mem_coe] using
    splitLastCoordinates_mem_rectangle d R ((splitLastCoordinates d).symm (y, t))

theorem mem_finiteShadow_splitLast_symm (G : Finset (∀ i, Box (Fin (d i))))
    (y : Fin (∑ i : Fin n, d i.castSucc) → ℝ) (t : Fin (d (Fin.last n)) → ℝ) :
    (splitLastCoordinates d).symm (y, t) ∈ finiteShadow G ↔
      y ∈ finiteShadow (finiteSlice G t) := by
  simp only [finiteShadow, Set.mem_iUnion]
  constructor
  · rintro ⟨R, hR, hx⟩
    obtain ⟨hy, ht⟩ := (mem_flatProductBox_splitLast_symm R y t).mp hx
    exact ⟨initialProjection R, Finset.mem_image.mpr
      ⟨R, Finset.mem_filter.mpr ⟨hR, ht⟩, rfl⟩, hy⟩
  · rintro ⟨P, hP, hy⟩
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨hRG, ht⟩ := Finset.mem_filter.mp hR
    exact ⟨R, hRG, (mem_flatProductBox_splitLast_symm R y t).mpr ⟨hy, ht⟩⟩

/-- No multiplicity is lost by the projected image of an incomparable slice. -/
theorem finiteOverlap_splitLast_symm
    (D : ∀ i, CubeGrid (d i)) (G : Finset (∀ i, Box (Fin (d i))))
    (hG : (↑G : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (y : Fin (∑ i : Fin n, d i.castSucc) → ℝ) (t : Fin (d (Fin.last n)) → ℝ) :
    finiteOverlap G ((splitLastCoordinates d).symm (y, t)) =
      finiteOverlap (finiteSlice G t) y := by
  have h := overlap_splitLast_symm D (↑G) hG hinc y t
  rw [← coe_finiteSlice G t, overlap_finset, overlap_finset] at h
  simpa only [ENNReal.toReal_ofReal (finiteOverlap_nonneg _ _)] using
    congrArg ENNReal.toReal h

/-- The measures of the slice shadows integrate to the full shadow. -/
theorem volume_finiteShadow_slices (G : Finset (∀ i, Box (Fin (d i)))) :
    volume (finiteShadow G) = ∫⁻ t, volume (finiteShadow (finiteSlice G t)) := by
  let f : (Fin (∑ i, d i) → ℝ) → ℝ≥0∞ :=
    (finiteShadow G).indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator (measurableSet_finiteShadow G)
  calc
    volume (finiteShadow G) = ∫⁻ x, f x := by
      simp [f, lintegral_indicator, measurableSet_finiteShadow]
    _ = ∫⁻ t, ∫⁻ y, f ((splitLastCoordinates d).symm (y, t)) :=
      lintegral_splitLastCoordinates d f hf
    _ = _ := by
      apply lintegral_congr
      intro t
      have hpoint : (fun y => f ((splitLastCoordinates d).symm (y, t))) =
          (finiteShadow (finiteSlice G t)).indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext y
        simp only [f, Set.indicator, mem_finiteShadow_splitLast_symm]
      rw [hpoint]
      simp [lintegral_indicator, measurableSet_finiteShadow]

end ReyZygmund.Geometry
