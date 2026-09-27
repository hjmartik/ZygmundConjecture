import ReyZygmund.Sharpness.SpatialFamily

/-! Expected propositions for the paper's spatial family. -/

open BoxIntegral
open scoped BigOperators Classical

namespace ReyZygmundVerification

open ReyZygmund.Geometry ReyZygmund.Sharpness

def sharpSpatialFamilyPartitionContract : Prop :=
  ∀ {n N : ℕ} {d : Fin (n + 3) → ℕ}, 2 ≤ N → ∀ (s : ℕ)
    (D : ∀ j, DyadicGrid (d j)) (Q : ∀ j, Box (Fin (d j))),
    (∀ j, Q j ∈ (D j).cubes 0) →
    ∀ (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ)))),
    (∀ i k R, R ∈ P i k →
      R ∈ (D i.succ).cubes ((s : ℤ) * selectionScale N i k)) →
    ∀ (a : Fin (n + 2) → Fin N),
    (∀ R ∈ sharpSpatialFamily s Q P a, ∀ j,
      R j ∈ (D j).cubes (sharpGeneration s a j)) ∧
      (⋃ R ∈ sharpSpatialFamily s Q P a, productBox R) =
        {x : ProductPoint d | x 0 ∈ Q 0 ∧
          ∀ i, x i.succ ∈ boxUnion (P i (a i).val)} ∧
      Set.PairwiseDisjoint
        (↑(sharpSpatialFamily s Q P a) : Set (∀ j, Box (Fin (d j)))) productBox ∧
      ∀ x : ProductPoint d,
        (∑ R ∈ sharpSpatialFamily s Q P a,
          (productBox R).indicator (fun _ => (1 : ℝ)) x) =
          (Q 0 : Set (Fin (d 0) → ℝ)).indicator (fun _ => (1 : ℝ)) (x 0) *
            ∏ i, (boxUnion (P i (a i).val)).indicator (fun _ => (1 : ℝ)) (x i.succ)

def sharpSpatialFamilyMembershipContract : Prop :=
  ∀ {n N : ℕ} {d : Fin (n + 3) → ℕ}, 2 ≤ N → ∀ (s : ℕ)
    (D : ∀ j, DyadicGrid (d j)) (Q : ∀ j, Box (Fin (d j))),
    (∀ j, Q j ∈ (D j).cubes 0) →
    ∀ (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ)))),
    (∀ i k R, R ∈ P i k →
      R ∈ (D i.succ).cubes ((s : ℤ) * selectionScale N i k)) →
    ∀ (a : Fin (n + 2) → Fin N) (R : ∀ j, Box (Fin (d j))),
    R ∈ sharpSpatialFamily s Q P a ↔
      (∀ j, R j ∈ (D j).cubes (sharpGeneration s a j)) ∧
      productBox R ⊆ {x : ProductPoint d | x 0 ∈ Q 0 ∧
        ∀ i, x i.succ ∈ boxUnion (P i (a i).val)}

def sharpSpatialTotalContract : Prop :=
  ∀ {n N : ℕ} {d : Fin (n + 3) → ℕ}, 2 ≤ N → ∀ (s : ℕ), 1 ≤ s →
    (∀ j, 0 < d j) → ∀ (D : ∀ j, DyadicGrid (d j))
      (Q : ∀ j, Box (Fin (d j))),
    (∀ j, Q j ∈ (D j).cubes 0) →
    ∀ (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ)))),
    (∀ i k R, R ∈ P i k →
      R ∈ (D i.succ).cubes ((s : ℤ) * selectionScale N i k)) →
    (∀ i, boxUnion (P i 0) = (Q i.succ : Set (Fin (d i.succ) → ℝ))) →
    (∀ i k, boxUnion (P i (k + 1)) ⊆ boxUnion (P i k)) →
    (↑(sharpSpatialTotal N s Q P) : Set (∀ j, Box (Fin (d j)))) ⊆
        ReyZygmund.Continuous.dyadicPhiRectangles D
          (fun k : Fin (n + 2) → ℤ => ∑ i, k i) ∧
      (∀ R ∈ sharpSpatialTotal N s Q P, ∀ S ∈ sharpSpatialTotal N s Q P,
        productBox R ⊆ productBox S → R = S) ∧
      (⋃ R ∈ sharpSpatialTotal N s Q P, productBox R) = productBox Q ∧
      ∀ R ∈ sharpSpatialTotal N s Q P,
        ∃! a : Fin (n + 2) → Fin N, R ∈ sharpSpatialFamily s Q P a

end ReyZygmundVerification
