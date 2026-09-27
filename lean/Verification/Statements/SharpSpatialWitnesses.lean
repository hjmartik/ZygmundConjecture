import ReyZygmund.Sharpness.SpatialWitnesses

/-! Statements about the disjoint subsets establishing sparseness and the resulting overlap. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmundVerification

open ReyZygmund.Geometry ReyZygmund.Sharpness

def sharpSpatialWitnessPropertiesContract : Prop :=
  ∀ {n N : ℕ} {d : Fin (n + 3) → ℕ}, 2 ≤ N → ∀ (s : ℕ)
    (D : ∀ j, DyadicGrid (d j)) (Q : ∀ j, Box (Fin (d j))),
    (∀ j, Q j ∈ (D j).cubes 0) →
    ∀ (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ)))),
    (∀ i k R, R ∈ P i k →
      R ∈ (D i.succ).cubes ((s : ℤ) * selectionScale N i k)) →
    (∀ (a : Fin (n + 2) → Fin N) i (I : Box (Fin (d i.succ))),
      I ∈ (D i.succ).cubes (sharpGeneration s a i.succ) →
      (I : Set (Fin (d i.succ) → ℝ)) ⊆ boxUnion (P i (a i).val) →
      volume.real ((I : Set (Fin (d i.succ) → ℝ)) ∩ boxUnion (P i ((a i).val + 1))) =
        (2 : ℝ) ^ (-(s : ℤ)) * volume.real (I : Set (Fin (d i.succ) → ℝ))) →
    ∀ (a : Fin (n + 2) → Fin N) (R : ∀ j, Box (Fin (d j))),
    R ∈ sharpSpatialFamily s Q P a →
    MeasurableSet (sharpSpatialWitness P a R) ∧
      sharpSpatialWitness P a R ⊆ productBox R ∧
      volume.real (sharpSpatialWitness P a R) =
        (1 - (2 : ℝ) ^ (-(s : ℤ))) ^ (n + 2) * volume.real (productBox R)

def sharpSpatialTotalWitnessesContract : Prop :=
  ∀ {n N : ℕ} {d : Fin (n + 3) → ℕ}, 2 ≤ N → ∀ (s : ℕ), 1 ≤ s →
    (∀ j, 0 < d j) → ∀ (D : ∀ j, DyadicGrid (d j))
      (Q : ∀ j, Box (Fin (d j))),
    (∀ j, Q j ∈ (D j).cubes 0) →
    ∀ (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ)))),
    (∀ i k R, R ∈ P i k →
      R ∈ (D i.succ).cubes ((s : ℤ) * selectionScale N i k)) →
    (∀ i, boxUnion (P i 0) = (Q i.succ : Set (Fin (d i.succ) → ℝ))) →
    (∀ i k, boxUnion (P i (k + 1)) ⊆ boxUnion (P i k)) →
    (∀ (a : Fin (n + 2) → Fin N) i (I : Box (Fin (d i.succ))),
      I ∈ (D i.succ).cubes (sharpGeneration s a i.succ) →
      (I : Set (Fin (d i.succ) → ℝ)) ⊆ boxUnion (P i (a i).val) →
      volume.real ((I : Set (Fin (d i.succ) → ℝ)) ∩ boxUnion (P i ((a i).val + 1))) =
        (2 : ℝ) ^ (-(s : ℤ)) * volume.real (I : Set (Fin (d i.succ) → ℝ))) →
    ∃ E : (∀ j, Box (Fin (d j))) → Set (ProductPoint d),
      (∀ (a : Fin (n + 2) → Fin N) R, R ∈ sharpSpatialFamily s Q P a →
        E R = sharpSpatialWitness P a R) ∧
      (∀ R ∈ sharpSpatialTotal N s Q P,
        MeasurableSet (E R) ∧ E R ⊆ productBox R ∧
          volume.real (E R) = (1 - (2 : ℝ) ^ (-(s : ℤ))) ^ (n + 2) *
            volume.real (productBox R)) ∧
      Set.PairwiseDisjoint (↑(sharpSpatialTotal N s Q P) :
        Set (∀ j, Box (Fin (d j)))) E

def sharpSpatialTotalOverlapContract : Prop :=
  ∀ {n N : ℕ} {d : Fin (n + 3) → ℕ}, 2 ≤ N → ∀ (s : ℕ), 1 ≤ s →
    (∀ j, 0 < d j) → ∀ (D : ∀ j, DyadicGrid (d j))
      (Q : ∀ j, Box (Fin (d j))),
    (∀ j, Q j ∈ (D j).cubes 0) →
    ∀ (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ)))),
    (∀ i k R, R ∈ P i k →
      R ∈ (D i.succ).cubes ((s : ℤ) * selectionScale N i k)) →
    (∀ i, boxUnion (P i 0) = (Q i.succ : Set (Fin (d i.succ) → ℝ))) →
    (∀ i k, boxUnion (P i (k + 1)) ⊆ boxUnion (P i k)) →
    ∀ x : ProductPoint d,
    (∑ R ∈ sharpSpatialTotal N s Q P, (productBox R).indicator (fun _ => (1 : ℝ)) x) =
      (Q 0 : Set (Fin (d 0) → ℝ)).indicator (fun _ => (1 : ℝ)) (x 0) *
        ∏ i : Fin (n + 2), ∑ k : Fin N,
          (boxUnion (P i k.val)).indicator (fun _ => (1 : ℝ)) (x i.succ)

def sharpSpatialTotalMaximumSetContract : Prop :=
  ∀ {n N : ℕ} {d : Fin (n + 3) → ℕ}, 2 ≤ N → ∀ (s : ℕ), 1 ≤ s →
    (∀ j, 0 < d j) → ∀ (D : ∀ j, DyadicGrid (d j))
      (Q : ∀ j, Box (Fin (d j))),
    (∀ j, Q j ∈ (D j).cubes 0) →
    ∀ (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ)))),
    (∀ i k R, R ∈ P i k →
      R ∈ (D i.succ).cubes ((s : ℤ) * selectionScale N i k)) →
    (∀ i, boxUnion (P i 0) = (Q i.succ : Set (Fin (d i.succ) → ℝ))) →
    (∀ i k, boxUnion (P i (k + 1)) ⊆ boxUnion (P i k)) →
    {x : ProductPoint d | (∑ R ∈ sharpSpatialTotal N s Q P,
      (productBox R).indicator (fun _ => (1 : ℝ)) x) = (N : ℝ) ^ (n + 2)} =
      {x : ProductPoint d | x 0 ∈ Q 0 ∧
        ∀ i, x i.succ ∈ boxUnion (P i (N - 1))}

end ReyZygmundVerification
