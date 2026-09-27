import ReyZygmund.Geometry.LastCoordinate
import ReyZygmund.Overlap.Finite

/-! # Finite slices, shadows and overlap

The finite slice is the image of exactly those rectangles whose last cube
contains the slicing point. Incomparability is used only to justify the
overlap reindexing, not the union or measure identities.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

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
    (D : ∀ i, DyadicGrid (d i)) (G : Finset (∀ i, Box (Fin (d i))))
    (hG : (↑G : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (y : Fin (∑ i : Fin n, d i.castSucc) → ℝ) (t : Fin (d (Fin.last n)) → ℝ) :
    finiteOverlap G ((splitLastCoordinates d).symm (y, t)) =
      finiteOverlap (finiteSlice G t) y := by
  have hinj : ∀ R ∈ G.filter (fun R => t ∈ R (Fin.last n)),
      ∀ S ∈ G.filter (fun S => t ∈ S (Fin.last n)),
        initialProjection R = initialProjection S → R = S := by
    intro R hR S hS heq
    exact (initialProjection_injOn D (↑G) hG hinc t)
      (Finset.mem_filter.mp hR) (Finset.mem_filter.mp hS) heq
  unfold finiteOverlap finiteSlice
  rw [Finset.sum_image hinj, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro R _
  by_cases ht : t ∈ R (Fin.last n)
  · by_cases hy : y ∈ (flatProductBox (initialProjection R) : Set (Fin (∑ i : Fin n, d i.castSucc) → ℝ))
    · have hx : (splitLastCoordinates d).symm (y, t) ∈
          (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) :=
        (mem_flatProductBox_splitLast_symm R y t).mpr ⟨hy, ht⟩
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy, ht]
    · have hx : (splitLastCoordinates d).symm (y, t) ∉
          (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) :=
        fun h => hy ((mem_flatProductBox_splitLast_symm R y t).mp h).1
      simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy, ht]
  · have hx : (splitLastCoordinates d).symm (y, t) ∉
        (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) :=
      fun h => ht ((mem_flatProductBox_splitLast_symm R y t).mp h).2
    simp [Set.indicator_of_notMem hx, ht]

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
