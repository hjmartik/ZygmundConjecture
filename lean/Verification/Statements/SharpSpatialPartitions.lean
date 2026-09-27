import ReyZygmund.Sharpness.SpatialPartitions

/-! Expected propositions for finite spatial refinement and products. -/

open BoxIntegral
open scoped BigOperators Classical

namespace ReyZygmundVerification

open ReyZygmund.Geometry ReyZygmund.Sharpness

def sharpSpatialRefinementContract : Prop :=
  ∀ {d : ℕ} (D : DyadicGrid d) (n g : ℤ), n ≤ g →
    ∀ (P : Finset (Box (Fin d))), (∀ Q ∈ P, Q ∈ D.cubes n) →
    let F := P.biUnion (fun Q => (level Q (g - n).toNat).boxes)
    (∀ R ∈ F, R ∈ D.cubes g) ∧
      boxUnion F = boxUnion P ∧
      Set.PairwiseDisjoint (↑F : Set (Box (Fin d)))
        (fun R => (R : Set (Fin d → ℝ))) ∧
      ∀ R ∈ F, ∃ Q ∈ P, R ≤ Q

def sharpSpatialProductPartitionContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ)
    (P : ∀ i, Finset (Box (Fin (d i)))),
    (∀ i Q, Q ∈ P i → Q ∈ (D i).cubes (n i)) →
    (⋃ R ∈ Fintype.piFinset P, productBox R) =
        Set.pi Set.univ (fun i => boxUnion (P i)) ∧
      Set.PairwiseDisjoint
        (↑(Fintype.piFinset P) : Set (∀ i, Box (Fin (d i)))) productBox ∧
      ∀ x : ProductPoint d,
        (∑ R ∈ Fintype.piFinset P,
          (productBox R).indicator (fun _ => (1 : ℝ)) x) =
          ∏ i, (boxUnion (P i)).indicator (fun _ => (1 : ℝ)) (x i)

end ReyZygmundVerification
