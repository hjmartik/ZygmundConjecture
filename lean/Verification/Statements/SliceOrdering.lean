import ReyZygmund.Geometry.SliceOrdering

/-! Explicit expected propositions for finite slice ordering and its range. -/

open BoxIntegral
open ReyZygmund.Geometry

namespace ReyZygmundVerification

def sliceEnumerationContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (D : ∀ i, DyadicGrid (d i)) (G : Finset (∀ i, Box (Fin (d i)))),
    (↑G : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D →
    ∀ t : Fin (d (Fin.last n)) → ℝ,
      ∃ N : ℕ, ∃ R : Fin N → (∀ i, Box (Fin (d i))),
        Function.Injective R ∧
        (∀ S : ∀ i, Box (Fin (d i)),
          S ∈ G ∧ t ∈ S (Fin.last n) ↔ ∃ i, R i = S) ∧
        (∀ i j : Fin N, i < j → R j (Fin.last n) ≤ R i (Fin.last n))

def sliceEnumerationProjectionRangeContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (G : Finset (∀ i, Box (Fin (d i)))) (t : Fin (d (Fin.last n)) → ℝ)
    {N : ℕ} (R : Fin N → (∀ i, Box (Fin (d i)))),
    (∀ S : ∀ i, Box (Fin (d i)),
      S ∈ G ∧ t ∈ S (Fin.last n) ↔ ∃ i, R i = S) →
    sliceFamily (↑G : Set (∀ i, Box (Fin (d i)))) t =
      Set.range (fun i => initialProjection (R i))

end ReyZygmundVerification
