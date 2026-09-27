import ReyZygmund.Sharpness.Construction

/-! Expected proposition for the finite product-coordinate construction. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmundVerification

open ReyZygmund.Geometry ReyZygmund.Sharpness

def sharpSpatialConstructionContract : Prop :=
  ∀ (n N s : ℕ), 2 ≤ N → 1 ≤ s → ∀ (d : Fin (n + 3) → ℕ),
    (∀ j, 0 < d j) → ∀ (D : ∀ j, DyadicGrid (d j))
      (Q : ∀ j, Box (Fin (d j))),
    (∀ j, Q j ∈ (D j).cubes 0) →
    ∃ G : Finset (∀ j, Box (Fin (d j))),
      ∃ E : (∀ j, Box (Fin (d j))) → Set (ProductPoint d),
        ∃ L : Set (ProductPoint d),
      (↑G : Set (∀ j, Box (Fin (d j)))) ⊆
        ReyZygmund.Continuous.dyadicPhiRectangles D
          (fun k : Fin (n + 2) → ℤ => ∑ i, k i) ∧
      (∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → R = S) ∧
      (⋃ R ∈ G, productBox R) = productBox Q ∧
      (∀ R ∈ G, MeasurableSet (E R) ∧ E R ⊆ productBox R ∧
        volume.real (E R) = (1 - (2 : ℝ) ^ (-(s : ℤ))) ^ (n + 2) *
          volume.real (productBox R)) ∧
      Set.PairwiseDisjoint (↑G : Set (∀ j, Box (Fin (d j)))) E ∧
      MeasurableSet L ∧ L ⊆ (⋃ R ∈ G, productBox R) ∧
      L = {x : ProductPoint d | (∑ R ∈ G,
        (productBox R).indicator (fun _ => (1 : ℝ)) x) = (N : ℝ) ^ (n + 2)} ∧
      volume.real L = ((2 : ℝ) ^ (-(s : ℤ))) ^ ((n + 2) * (N - 1)) *
        volume.real (productBox Q)

end ReyZygmundVerification
