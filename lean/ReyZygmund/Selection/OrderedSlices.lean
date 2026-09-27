import ReyZygmund.Geometry.FiniteAverages
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith

/-! # Half-sparseness of ordered slices

The last cube factors decrease in the given order. Deleting earlier
first-coordinate boxes from each first-coordinate box gives disjoint subsets of at
least half its volume, by the product-overlap bound. This argument needs neither a
grid nor positive coordinate dimensions.
-/

open BoxIntegral MeasureTheory
open scoped Classical ENNReal

namespace ReyZygmund.Selection

open Geometry

private theorem real_volume_product {a b : ℕ}
    (A : Set (Fin a → ℝ)) (B : Set (Fin b → ℝ)) :
    volume.real (A ×ˢ B) = volume.real A * volume.real B := by
  exact measureReal_prod_prod (μ := volume) (ν := volume) A B

private theorem volume_product_box_ne_top {a b : ℕ}
    (R : Box (Fin a)) (C : Box (Fin b)) :
    volume ((R : Set (Fin a → ℝ)) ×ˢ (C : Set (Fin b → ℝ))) ≠ ∞ := by
  change ((volume : Measure (Fin a → ℝ)).prod (volume : Measure (Fin b → ℝ)))
    ((R : Set (Fin a → ℝ)) ×ˢ (C : Set (Fin b → ℝ))) ≠ ∞
  rw [Measure.prod_prod]
  exact (ENNReal.mul_lt_top R.isBounded.measure_lt_top C.isBounded.measure_lt_top).ne

/-- Deleting earlier first-coordinate boxes gives measurable disjoint subsets of at
least half the required volume, when last-coordinate boxes decrease and each
product box overlaps the others in at most half its volume. -/
theorem ordered_slice_half_sparse {a b N : ℕ}
    (R : Fin N → Box (Fin a)) (C : Fin N → Box (Fin b))
    (horder : ∀ i j : Fin N, i < j → C j ≤ C i)
    (hoverlap : ∀ i : Fin N,
      volume.real (((R i : Set (Fin a → ℝ)) ×ˢ (C i : Set (Fin b → ℝ))) ∩
        ⋃ j : Fin N, ⋃ (_ : j ≠ i),
          ((R j : Set (Fin a → ℝ)) ×ˢ (C j : Set (Fin b → ℝ)))) ≤
        (1 / 2 : ℝ) *
          volume.real ((R i : Set (Fin a → ℝ)) ×ˢ (C i : Set (Fin b → ℝ)))) :
    let E : Fin N → Set (Fin a → ℝ) := fun i =>
      (R i : Set (Fin a → ℝ)) \ ⋃ j : Fin N, ⋃ (_ : j < i), (R j : Set (Fin a → ℝ))
    (∀ i, MeasurableSet (E i) ∧ E i ⊆ (R i : Set (Fin a → ℝ)) ∧
      (1 / 2 : ℝ) * volume.real (R i : Set (Fin a → ℝ)) ≤ volume.real (E i)) ∧
      Pairwise (fun i j => Disjoint (E i) (E j)) := by
  let U : Fin N → Set (Fin a → ℝ) := fun i =>
    ⋃ j : Fin N, ⋃ (_ : j < i), (R j : Set (Fin a → ℝ))
  have hU (i : Fin N) : MeasurableSet (U i) :=
    MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun _ => (R j).measurableSet_coe))
  change (∀ i, MeasurableSet ((R i : Set (Fin a → ℝ)) \ U i) ∧
      (R i : Set (Fin a → ℝ)) \ U i ⊆ (R i : Set (Fin a → ℝ)) ∧
      (1 / 2 : ℝ) * volume.real (R i : Set (Fin a → ℝ)) ≤
        volume.real ((R i : Set (Fin a → ℝ)) \ U i)) ∧
    Pairwise (fun i j => Disjoint ((R i : Set (Fin a → ℝ)) \ U i) ((R j : Set (Fin a → ℝ)) \ U j))
  constructor
  · intro i
    refine ⟨(R i).measurableSet_coe.diff (hU i), Set.sdiff_subset, ?_⟩
    have hsub : (((R i : Set (Fin a → ℝ)) ∩ U i) ×ˢ (C i : Set (Fin b → ℝ))) ⊆
        (((R i : Set (Fin a → ℝ)) ×ˢ (C i : Set (Fin b → ℝ))) ∩
          ⋃ j : Fin N, ⋃ (_ : j ≠ i), ((R j : Set (Fin a → ℝ)) ×ˢ (C j : Set (Fin b → ℝ)))) := by
      rintro ⟨x, y⟩ ⟨⟨hxR, hxU⟩, hyC⟩
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxU
      obtain ⟨hji, hxj⟩ := Set.mem_iUnion.mp hj
      refine ⟨⟨hxR, hyC⟩, Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ?_⟩⟩
      exact ⟨ne_of_lt hji, hxj, horder j i hji hyC⟩
    have hfinite : volume (((R i : Set (Fin a → ℝ)) ×ˢ (C i : Set (Fin b → ℝ))) ∩
        ⋃ j : Fin N, ⋃ (_ : j ≠ i), ((R j : Set (Fin a → ℝ)) ×ˢ (C j : Set (Fin b → ℝ)))) ≠ ∞ :=
      measure_ne_top_of_subset Set.inter_subset_left (volume_product_box_ne_top (R i) (C i))
    have hprod := (measureReal_mono hsub hfinite).trans (hoverlap i)
    simp only [real_volume_product] at hprod
    have hmass : volume.real ((R i : Set (Fin a → ℝ)) ∩ U i) ≤
        (1 / 2 : ℝ) * volume.real (R i : Set (Fin a → ℝ)) := by
      exact le_of_mul_le_mul_right (a := volume.real (C i : Set (Fin b → ℝ)))
        (by simpa only [mul_assoc] using hprod) (box_volume_pos (C i))
    have hsplit := measureReal_inter_add_sdiff (μ := volume)
      (s := (R i : Set (Fin a → ℝ))) (hU i) (R i).isBounded.measure_lt_top.ne
    linarith
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · apply Set.disjoint_left.mpr
      intro x hxi hxj
      exact hxj.2 (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hij, hxi.1⟩⟩)
    · apply Set.disjoint_left.mpr
      intro x hxi hxj
      exact hxi.2 (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hji, hxj.1⟩⟩)

end ReyZygmund.Selection
