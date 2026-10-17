import ReyZygmund.Sharpness.Construction

/-! Expected proposition for the finite product-coordinate construction. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

open ReyZygmund.MathlibOnly (CubeGrid)

namespace ReyZygmundVerification

open ReyZygmund.Geometry ReyZygmund.Sharpness

def sharpSpatialConstructionContract : Prop :=
  ∀ (n N s : ℕ), 2 ≤ N → 1 ≤ s → ∀ (d : Fin (n + 3) → ℕ),
    (∀ j, 0 < d j) → ∀ (D : ∀ j, CubeGrid (d j))
      (Q : ∀ j, Box (Fin (d j))),
    (∀ j, Q j ∈ (D j).cubesAtGeneration 0) →
    ∃ G : Finset (∀ j, Box (Fin (d j))),
      ∃ E : (∀ j, Box (Fin (d j))) → Set (ProductPoint d),
        ∃ L : Set (ProductPoint d),
      (↑G : Set (∀ j, Box (Fin (d j)))) ⊆
        ReyZygmund.MathlibOnly.dyadicZygmundRectangles D
          (fun k : Fin (n + 2) → ℤ => ∑ i, k i) ∧
      (∀ R ∈ G, ∀ S ∈ G, productRectangle R ⊆ productRectangle S → R = S) ∧
      (⋃ R ∈ G, productRectangle R) = productRectangle Q ∧
      (∀ R ∈ G, MeasurableSet (E R) ∧ E R ⊆ productRectangle R ∧
        volume.real (E R) = (1 - (2 : ℝ) ^ (-(s : ℤ))) ^ (n + 2) *
          volume.real (productRectangle R)) ∧
      Set.PairwiseDisjoint (↑G : Set (∀ j, Box (Fin (d j)))) E ∧
      MeasurableSet L ∧ L ⊆ (⋃ R ∈ G, productRectangle R) ∧
      L = {x : ProductPoint d | (∑ R ∈ G,
        (productRectangle R).indicator (fun _ => (1 : ℝ)) x) = (N : ℝ) ^ (n + 2)} ∧
      volume.real L = ((2 : ℝ) ^ (-(s : ℤ))) ^ ((n + 2) * (N - 1)) *
        volume.real (productRectangle Q)

end ReyZygmundVerification
