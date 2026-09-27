import ReyZygmund.Selection.OrderedSlices

/-! Statement of half-sparseness for ordered slices. -/

open BoxIntegral MeasureTheory

namespace ReyZygmundVerification

def orderedSliceHalfSparseContract : Prop :=
  ∀ {a b N : ℕ} (R : Fin N → Box (Fin a)) (C : Fin N → Box (Fin b)),
    (∀ i j : Fin N, i < j → C j ≤ C i) →
    (∀ i : Fin N,
      volume.real (((R i : Set (Fin a → ℝ)) ×ˢ (C i : Set (Fin b → ℝ))) ∩
        ⋃ j : Fin N, ⋃ (_ : j ≠ i),
          ((R j : Set (Fin a → ℝ)) ×ˢ (C j : Set (Fin b → ℝ)))) ≤
        (1 / 2 : ℝ) *
          volume.real ((R i : Set (Fin a → ℝ)) ×ˢ (C i : Set (Fin b → ℝ)))) →
    let E : Fin N → Set (Fin a → ℝ) := fun i =>
      (R i : Set (Fin a → ℝ)) \ ⋃ j : Fin N, ⋃ (_ : j < i), (R j : Set (Fin a → ℝ))
    (∀ i, MeasurableSet (E i) ∧ E i ⊆ (R i : Set (Fin a → ℝ)) ∧
      (1 / 2 : ℝ) * volume.real (R i : Set (Fin a → ℝ)) ≤ volume.real (E i)) ∧
      Pairwise (fun i j => Disjoint (E i) (E j))

end ReyZygmundVerification
