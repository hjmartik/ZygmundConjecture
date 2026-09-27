import ReyZygmund.Maximal.Euclidean
import ReyZygmund.Overlap.Finite
import Mathlib.MeasureTheory.Measure.Continuity

/-! # Finite shadows exhaust a strict maximal level set

The strict level set is the union of rectangles whose coefficient in
`euclideanFamilyMaximal` exceeds the threshold. Finite unions exhaust this set for
a countable family. The set identity is algebraic and permits arbitrary input; its
use for averages in the endpoint theorem requires local integrability.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry Overlap

variable {m : ℕ} {d : Fin m → ℕ}

/-- The strict level set is the union of rectangles whose normalized integral of `|f|`
exceeds the positive threshold. This pointwise identity does not require
countability. -/
theorem euclidean_levelset_eq_iUnion
    (G : Set (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (lam : ℝ) (hlam : 0 < lam) :
    {x | ENNReal.ofReal lam < euclideanFamilyMaximal G f x} =
      ⋃ R ∈ G, ⋃ (_ : lam <
        (∫ y in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), |f y|) /
          volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))),
        (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) := by
  ext x
  change (ENNReal.ofReal lam < euclideanFamilyMaximal G f x) ↔ _
  rw [euclideanFamilyMaximal, lt_iSup_iff]
  constructor
  · rintro ⟨R, hR⟩
    have hxR : x ∈ (flatProductBox R.1 : Set (Fin (∑ i, d i) → ℝ)) := by
      by_contra hxR
      rw [Set.indicator_of_notMem hxR, ENNReal.ofReal_zero] at hR
      exact (not_lt_of_ge (zero_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal lam)) hR
    rw [Set.indicator_of_mem hxR] at hR
    exact Set.mem_iUnion₂.mpr ⟨R.1, R.2, Set.mem_iUnion.mpr
      ⟨(ENNReal.ofReal_lt_ofReal_iff_of_nonneg hlam.le).mp hR, hxR⟩⟩
  · intro hx
    obtain ⟨R, hR, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨hmean, hxR⟩ := Set.mem_iUnion.mp hx
    refine ⟨⟨R, hR⟩, ?_⟩
    rw [Set.indicator_of_mem hxR]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hlam.le).mpr hmean

/-- A uniform estimate for all finite high-average shadows bounds the countable
family's strict level set. No finite total shadow, nonemptiness, grid or common
top rectangle is needed. -/
theorem euclidean_levelset_measure_le_of_finite_shadows
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G.Countable)
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (lam : ℝ) (hlam : 0 < lam) (C : ℝ≥0∞)
    (hfinite : ∀ F : Finset (∀ i, Box (Fin (d i))),
      (↑F : Set (∀ i, Box (Fin (d i)))) ⊆ G →
      (∀ R ∈ F, lam <
        (∫ y in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), |f y|) /
          volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) →
      volume (finiteShadow F) ≤ C) :
    volume {x | ENNReal.ofReal lam < euclideanFamilyMaximal G f x} ≤ C := by
  let H : Set (∀ i, Box (Fin (d i))) := {R | R ∈ G ∧ lam <
    (∫ y in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), |f y|) /
      volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))}
  have hH : H.Countable := hG.mono (fun _ h => h.1)
  have := hH.to_subtype
  let S : Finset H → Set (Fin (∑ i, d i) → ℝ) :=
    fun F => finiteShadow (F.image Subtype.val)
  have hmono : Monotone S := by
    intro F K hFK x hx
    obtain ⟨R, hR, hxR⟩ := Set.mem_iUnion₂.mp hx
    exact flatProductBox_subset_finiteShadow (K.image Subtype.val) R
      (Finset.image_mono Subtype.val hFK hR) hxR
  have hdir : Directed (· ⊆ ·) S := by
    intro F K
    exact ⟨F ∪ K, hmono Finset.subset_union_left, hmono Finset.subset_union_right⟩
  have hlevel : {x | ENNReal.ofReal lam < euclideanFamilyMaximal G f x} =
      ⋃ F : Finset H, S F := by
    rw [euclidean_levelset_eq_iUnion G f lam hlam]
    ext x
    constructor
    · intro hx
      obtain ⟨R, hR, hx⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨hmean, hxR⟩ := Set.mem_iUnion.mp hx
      let Q : H := ⟨R, hR, hmean⟩
      refine Set.mem_iUnion.mpr ⟨{Q}, ?_⟩
      exact flatProductBox_subset_finiteShadow (({Q} : Finset H).image Subtype.val) R
        (Finset.mem_image.mpr ⟨Q, Finset.mem_singleton_self Q, rfl⟩) hxR
    · intro hx
      obtain ⟨F, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨R, hR, hxR⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨Q, _hQ, rfl⟩ := Finset.mem_image.mp hR
      exact Set.mem_iUnion₂.mpr ⟨Q.1, Q.2.1, Set.mem_iUnion.mpr ⟨Q.2.2, hxR⟩⟩
  have hbound (F : Finset H) : volume (S F) ≤ C := by
    apply hfinite (F.image Subtype.val)
    · intro R hR
      obtain ⟨Q, _hQ, rfl⟩ := Finset.mem_image.mp hR
      exact Q.2.1
    · intro R hR
      obtain ⟨Q, _hQ, rfl⟩ := Finset.mem_image.mp hR
      exact Q.2.2
  rw [hlevel, hdir.measure_iUnion]
  exact iSup_le hbound

end ReyZygmund
