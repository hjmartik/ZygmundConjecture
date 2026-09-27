import ReyZygmund.Geometry.LastCoordinate
import ReyZygmund.Geometry.SliceOrdering
import ReyZygmund.Selection.OrderedSlices
import ReyZygmund.Overlap.Finite

/-! # Half-sparseness of a finite slice

Split off the last coordinate and order the rectangles through the slice. The
half-overlap bound gives disjoint subsets of at least half each projected rectangle's
volume. Finite unions over equal projections index these subsets by the slice family.
Incomparability, rounding and joint measurability in the slice parameter are not
required.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Selection

open Geometry Overlap

variable {n : ℕ} {d : Fin (n + 1) → ℕ}

private theorem enumerated_product_half_overlap
    (G : Finset (∀ i, Box (Fin (d i))))
    (hoverlap : ∀ R ∈ G,
      volume.real ((flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ∩
        finiteShadow (G.erase R)) ≤
        (1 / 2 : ℝ) * volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)))
    {N : ℕ} (R : Fin N → (∀ i, Box (Fin (d i))))
    (hinj : Function.Injective R) (hRG : ∀ i, R i ∈ G) (i : Fin N) :
    volume.real
      (((flatProductBox (initialProjection (R i)) :
          Set (Fin (∑ k : Fin n, d k.castSucc) → ℝ)) ×ˢ
        (R i (Fin.last n) : Set (Fin (d (Fin.last n)) → ℝ))) ∩
        ⋃ j : Fin N, ⋃ (_ : j ≠ i),
          ((flatProductBox (initialProjection (R j)) :
            Set (Fin (∑ k : Fin n, d k.castSucc) → ℝ)) ×ˢ
            (R j (Fin.last n) : Set (Fin (d (Fin.last n)) → ℝ)))) ≤
      (1 / 2 : ℝ) * volume.real
        ((flatProductBox (initialProjection (R i)) :
          Set (Fin (∑ k : Fin n, d k.castSucc) → ℝ)) ×ˢ
          (R i (Fin.last n) : Set (Fin (d (Fin.last n)) → ℝ))) := by
  let e := splitLastCoordinates d
  let P : Fin N → Set ((Fin (∑ k : Fin n, d k.castSucc) → ℝ) ×
      (Fin (d (Fin.last n)) → ℝ)) := fun j =>
    (flatProductBox (initialProjection (R j)) :
      Set (Fin (∑ k : Fin n, d k.castSucc) → ℝ)) ×ˢ
      (R j (Fin.last n) : Set (Fin (d (Fin.last n)) → ℝ))
  let A := P i ∩ ⋃ j : Fin N, ⋃ (_ : j ≠ i), P j
  have hpre : e ⁻¹' P i =
      (flatProductBox (R i) : Set (Fin (∑ k, d k) → ℝ)) := by
    ext x
    exact (splitLastCoordinates_mem_rectangle d (R i) x).symm
  have hvol : volume.real (flatProductBox (R i) : Set (Fin (∑ k, d k) → ℝ)) =
      volume.real (P i) := by
    have h := congrArg ENNReal.toReal
      ((volume_preserving_splitLastCoordinates d).measure_preimage_equiv (P i))
    change volume.real (e ⁻¹' P i) = volume.real (P i) at h
    rwa [hpre] at h
  have hsub : e ⁻¹' A ⊆
      (flatProductBox (R i) : Set (Fin (∑ k, d k) → ℝ)) ∩
        finiteShadow (G.erase (R i)) := by
    intro x hx
    change e x ∈ P i ∩ ⋃ j : Fin N, ⋃ (_ : j ≠ i), P j at hx
    obtain ⟨j, hji, hxj⟩ := Set.mem_iUnion₂.mp hx.2
    have hj : R j ∈ G.erase (R i) :=
      Finset.mem_erase.mpr ⟨fun h => hji (hinj h), hRG j⟩
    exact ⟨(splitLastCoordinates_mem_rectangle d (R i) x).mpr hx.1,
      flatProductBox_subset_finiteShadow (G.erase (R i)) (R j) hj
        ((splitLastCoordinates_mem_rectangle d (R j) x).mpr hxj)⟩
  have hfinite : volume
      ((flatProductBox (R i) : Set (Fin (∑ k, d k) → ℝ)) ∩
        finiteShadow (G.erase (R i))) ≠ ∞ :=
    measure_ne_top_of_subset Set.inter_subset_left
      (flatProductBox (R i)).isBounded.measure_lt_top.ne
  have hA : volume.real (e ⁻¹' A) = volume.real A :=
    congrArg ENNReal.toReal
      ((volume_preserving_splitLastCoordinates d).measure_preimage_equiv A)
  change volume.real A ≤ (1 / 2 : ℝ) * volume.real (P i)
  calc
    volume.real A = volume.real (e ⁻¹' A) := hA.symm
    _ ≤ volume.real
        ((flatProductBox (R i) : Set (Fin (∑ k, d k) → ℝ)) ∩
          finiteShadow (G.erase (R i))) := measureReal_mono hsub hfinite
    _ ≤ (1 / 2 : ℝ) *
        volume.real (flatProductBox (R i) : Set (Fin (∑ k, d k) → ℝ)) :=
      hoverlap (R i) (hRG i)
    _ = (1 / 2 : ℝ) * volume.real (P i) := by rw [hvol]

/-- Each fixed slice of a finite grid family satisfying the half-overlap bound is
half-sparse. Its disjoint measurable subsets are indexed by the projected
rectangles. -/
theorem finite_slice_half_sparse
    (D : ∀ i, DyadicGrid (d i)) (G : Finset (∀ i, Box (Fin (d i))))
    (hG : (↑G : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D)
    (hoverlap : ∀ R ∈ G,
      volume.real ((flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ∩
        finiteShadow (G.erase R)) ≤
        (1 / 2 : ℝ) * volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)))
    (t : Fin (d (Fin.last n)) → ℝ) :
    ∃ E : (∀ i : Fin n, Box (Fin (d i.castSucc))) →
        Set (Fin (∑ i : Fin n, d i.castSucc) → ℝ),
      (∀ P ∈ sliceFamily (↑G : Set (∀ i, Box (Fin (d i)))) t,
        MeasurableSet (E P) ∧
        E P ⊆ (flatProductBox P : Set (Fin (∑ i : Fin n, d i.castSucc) → ℝ)) ∧
        ENNReal.ofReal (1 / 2 : ℝ) *
          volume (flatProductBox P : Set (Fin (∑ i : Fin n, d i.castSucc) → ℝ)) ≤
          volume (E P)) ∧
      (sliceFamily (↑G : Set (∀ i, Box (Fin (d i)))) t).Pairwise
        (fun P Q => Disjoint (E P) (E Q)) := by
  obtain ⟨N, R, hinj, hrange, horder⟩ := exists_ordered_slice_enumeration D G hG t
  have hRG (i : Fin N) : R i ∈ G := ((hrange (R i)).mpr ⟨i, rfl⟩).1
  let B : Fin N → Box (Fin (∑ i : Fin n, d i.castSucc)) :=
    fun i => flatProductBox (initialProjection (R i))
  let C : Fin N → Box (Fin (d (Fin.last n))) := fun i => R i (Fin.last n)
  let E₀ : Fin N → Set (Fin (∑ i : Fin n, d i.castSucc) → ℝ) := fun i =>
    (B i : Set (Fin (∑ k : Fin n, d k.castSucc) → ℝ)) \
      ⋃ j : Fin N, ⋃ (_ : j < i),
        (B j : Set (Fin (∑ k : Fin n, d k.castSucc) → ℝ))
  have hordered :
      (∀ i, MeasurableSet (E₀ i) ∧
        E₀ i ⊆ (B i : Set (Fin (∑ k : Fin n, d k.castSucc) → ℝ)) ∧
        (1 / 2 : ℝ) * volume.real (B i : Set (Fin (∑ k : Fin n, d k.castSucc) → ℝ)) ≤
          volume.real (E₀ i)) ∧ Pairwise (fun i j => Disjoint (E₀ i) (E₀ j)) :=
    ordered_slice_half_sparse B C horder
      (enumerated_product_half_overlap G hoverlap R hinj hRG)
  have hmass (i : Fin N) : ENNReal.ofReal (1 / 2 : ℝ) *
      volume (B i : Set (Fin (∑ k : Fin n, d k.castSucc) → ℝ)) ≤ volume (E₀ i) := by
    have h : ENNReal.ofReal ((1 / 2 : ℝ) *
        volume.real (B i : Set (Fin (∑ k : Fin n, d k.castSucc) → ℝ))) ≤
        volume (E₀ i) := ENNReal.ofReal_le_of_le_toReal (hordered.1 i).2.2
    rwa [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ofReal_measureReal (B i).isBounded.measure_lt_top.ne] at h
  let E : (∀ i : Fin n, Box (Fin (d i.castSucc))) →
      Set (Fin (∑ i : Fin n, d i.castSucc) → ℝ) := fun P =>
    ⋃ i : Fin N, ⋃ (_ : initialProjection (R i) = P), E₀ i
  have hfamily := sliceFamily_eq_range_of_enumeration G t R hrange
  refine ⟨E, ?_, ?_⟩
  · intro P hP
    refine ⟨?_, ?_, ?_⟩
    · exact MeasurableSet.iUnion (fun i =>
        MeasurableSet.iUnion (fun _ => (hordered.1 i).1))
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
      have h := (hordered.1 i).2.1 hxi
      simpa only [B, hi] using h
    · rw [hfamily] at hP
      obtain ⟨i, hi⟩ := hP
      have hsub : E₀ i ⊆ E P := fun _ hx => Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩
      have h := (hmass i).trans (measure_mono hsub)
      simpa only [B, hi] using h
  · intro P _hP Q _hQ hPQ
    apply Set.disjoint_left.mpr
    intro x hxP hxQ
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxP
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hxQ
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hPQ (hi.symm.trans hj)
    exact Set.disjoint_left.mp (hordered.2 hij) hxi hxj

end ReyZygmund.Selection
