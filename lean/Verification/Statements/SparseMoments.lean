import ReyZygmund.Overlap.FiniteMoments

/-! The finite sparse moment statement, with real moment order and disjoint measurable subsets establishing sparseness. -/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry ReyZygmund.Overlap

def finiteWeakerSparseMomentContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ},
    2 ≤ m → (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (G : Finset (∀ i, Box (Fin (d i)))),
    ↑G ⊆ gridRectangles D →
    (∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i) →
    ∀ eta : ℝ, 0 < eta →
    ∀ E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ),
    (∀ R ∈ G, MeasurableSet (E R)) →
    (∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) →
    Set.Pairwise (G : Set _) (fun R S => Disjoint (E R) (E S)) →
    (∀ R ∈ G, ENNReal.ofReal eta *
      volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤ volume (E R)) →
    ∀ q : ℝ, 2 ≤ q →
    Real.rpow (∫ x, Real.rpow (finiteOverlap G x) q) (1 / q) ≤
      (maximalDimensionConstant d + 3) * eta⁻¹ * q ^ (m - 1) *
        Real.rpow (volume.real (finiteShadow G)) (1 / q)

end ReyZygmundVerification
