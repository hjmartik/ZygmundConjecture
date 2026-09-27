import ReyZygmund.Geometry.GridFamilies
import ReyZygmund.Geometry.ProductContainment

/-! Independent explicit propositions for the paper's averaging-family
definition and both original-family inclusion conclusions. -/

open BoxIntegral
open scoped Classical

namespace ReyZygmundVerification

open ReyZygmund.Geometry ReyZygmund.Projection

def sourceAveragingMembershipContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ), (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
      (I : ∀ i, Box (Fin (d i))), (∀ i, I i ∈ (D i).cubes (n i)) →
      (∀ i, n i ≤ k) → ∀ (G : Finset (∀ i, Box (Fin (d i))))
        (R : ∀ i, Box (Fin (d i))),
        R ∈ averagingRectangles I (fun i => (k - n i).toNat) G ↔
          (R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
            ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u) ∧
            ∃ j : Fin m, R j ∈ partitionCubes (I j) (k - n j).toNat
              (eligibleProjections j G R)

def sourceOriginalPartitionContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ), (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
      (I : ∀ i, Box (Fin (d i))), (∀ i, I i ∈ (D i).cubes (n i)) →
      (∀ i, n i ≤ k) → ∀ (G : Finset (∀ i, Box (Fin (d i)))),
        (∀ R ∈ G, R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
          ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u) →
        (∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → R = S) →
        ∀ (R : ∀ i, Box (Fin (d i))), R ∈ G → ∀ (j : Fin m),
          R j ∈ partitionCubes (I j) (k - n j).toNat (eligibleProjections j G R)

def sourceOriginalSubsetAveragingContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ), (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
      (I : ∀ i, Box (Fin (d i))), (∀ i, I i ∈ (D i).cubes (n i)) →
      (∀ i, n i ≤ k) → ∀ (G : Finset (∀ i, Box (Fin (d i)))),
        (∀ R ∈ G, R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
          ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u) →
        (∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → R = S) →
        0 < m → G ⊆ averagingRectangles I (fun i => (k - n i).toNat) G

end ReyZygmundVerification
