import ReyZygmund.Selection.SliceSparsity

/-! Explicit expected proposition for finite slice half-sparseness. -/

open BoxIntegral MeasureTheory
open ReyZygmund.Geometry ReyZygmund.Overlap
open scoped BigOperators ENNReal Classical

namespace ReyZygmundVerification

def finiteSliceHalfSparseContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (D : ∀ i, DyadicGrid (d i)) (G : Finset (∀ i, Box (Fin (d i)))),
    (↑G : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D →
    (∀ R ∈ G,
      volume.real ((flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ∩
        finiteShadow (G.erase R)) ≤
        (1 / 2 : ℝ) * volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) →
    ∀ t : Fin (d (Fin.last n)) → ℝ,
      ∃ E : (∀ i : Fin n, Box (Fin (d i.castSucc))) →
          Set (Fin (∑ i : Fin n, d i.castSucc) → ℝ),
        (∀ P ∈ sliceFamily (↑G : Set (∀ i, Box (Fin (d i)))) t,
          MeasurableSet (E P) ∧
          E P ⊆ (flatProductBox P : Set (Fin (∑ i : Fin n, d i.castSucc) → ℝ)) ∧
          ENNReal.ofReal (1 / 2 : ℝ) *
            volume (flatProductBox P : Set (Fin (∑ i : Fin n, d i.castSucc) → ℝ)) ≤
            volume (E P)) ∧
        (sliceFamily (↑G : Set (∀ i, Box (Fin (d i)))) t).Pairwise
          (fun P Q => Disjoint (E P) (E Q))

end ReyZygmundVerification
