import ReyZygmund.Sharpness.CoordinateRetention

/-! Expected propositions for the paper's coordinate retention schedules. -/

open BoxIntegral MeasureTheory
open scoped Classical

namespace ReyZygmundVerification

open ReyZygmund.Geometry ReyZygmund.Sharpness

def sharpSelectionScaleNatContract : Prop :=
  ∀ {n N : ℕ}, 2 ≤ N → ∀ (i : Fin (n + 2)) (k : ℕ),
    ((selectionScale N i k).toNat : ℤ) = selectionScale N i k

def sharpCoordinateRetentionContract : Prop :=
  ∀ (n N s : ℕ), 2 ≤ N → ∀ (d : Fin (n + 2) → ℕ),
    (∀ i, 0 < d i) → ∀ (D : ∀ i, DyadicGrid (d i))
      (Q : ∀ i, Box (Fin (d i))),
    (∀ i, Q i ∈ (D i).cubes 0) →
    ∃ P : ∀ i, ℕ → Finset (Box (Fin (d i))),
      (∀ i, P i 0 = (level (Q i) (s * (selectionScale N i 0).toNat)).boxes) ∧
      (∀ i, boxUnion (P i 0) = (Q i : Set (Fin (d i) → ℝ))) ∧
      (∀ i k R, R ∈ P i k →
        R ∈ (D i).cubes ((s : ℤ) * selectionScale N i k)) ∧
      (∀ i k, Set.PairwiseDisjoint (↑(P i k) : Set (Box (Fin (d i))))
        (fun R => (R : Set (Fin (d i) → ℝ)))) ∧
      (∀ i k, boxUnion (P i (k + 1)) ⊆ boxUnion (P i k)) ∧
      (∀ i k, MeasurableSet (boxUnion (P i k)) ∧ volume (boxUnion (P i k)) < ⊤) ∧
      (∀ i k, volume.real (boxUnion (P i k)) =
        ((2 : ℝ) ^ (-(s : ℤ))) ^ k * volume.real (Q i : Set (Fin (d i) → ℝ))) ∧
      (∀ (a : Fin (n + 2) → Fin N) i (I : Box (Fin (d i))),
        I ∈ (D i).cubes (sharpGeneration s a i.succ) →
        (I : Set (Fin (d i) → ℝ)) ⊆ boxUnion (P i (a i).val) →
        volume.real ((I : Set (Fin (d i) → ℝ)) ∩ boxUnion (P i ((a i).val + 1))) =
          (2 : ℝ) ^ (-(s : ℤ)) * volume.real (I : Set (Fin (d i) → ℝ)))

end ReyZygmundVerification
