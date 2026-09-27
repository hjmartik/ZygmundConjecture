import ReyZygmund.Overlap.FiniteExponential

/-! Explicit finite half-sparse overlap proposition used on slices. -/

open BoxIntegral MeasureTheory
open ReyZygmund.Geometry ReyZygmund.Overlap
open scoped BigOperators ENNReal Classical

namespace ReyZygmundVerification

def finiteHalfSparseExponentialContract : Prop :=
  ∃ c B : ℕ → ℕ → ℝ,
    (∀ m D, 0 < c m D) ∧ (∀ m D, 0 < B m D) ∧
    ∀ (m : ℕ) (d : Fin m → ℕ), 2 ≤ m → (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (G : Finset (∀ i, Box (Fin (d i)))),
    (↑G : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D →
    (∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i) →
    ∀ E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ),
    (∀ R ∈ G, MeasurableSet (E R)) →
    (∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) →
    Set.Pairwise (↑G) (fun R S => Disjoint (E R) (E S)) →
    (∀ R ∈ G, ENNReal.ofReal (1 / 2 : ℝ) *
      volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤ volume (E R)) →
    (∫⁻ x in finiteShadow G, ENNReal.ofReal
      (Real.exp (c m (∑ i, d i) *
        Real.rpow (finiteOverlap G x) (1 / ((m - 1 : ℕ) : ℝ))))) ≤
      ENNReal.ofReal (B m (∑ i, d i)) * volume (finiteShadow G)

end ReyZygmundVerification
