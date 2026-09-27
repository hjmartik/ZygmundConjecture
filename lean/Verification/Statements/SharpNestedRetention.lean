import ReyZygmund.Sharpness.NestedRetention

/-! Expected proposition for the nested retention sequence. -/

open BoxIntegral MeasureTheory
open scoped Classical

namespace ReyZygmundVerification

open ReyZygmund.Geometry ReyZygmund.Sharpness

def sharpNestedRetentionContract : Prop :=
  ∀ {d : ℕ}, 0 < d → ∀ (D : DyadicGrid d) (Q : Box (Fin d)), Q ∈ D.cubes 0 →
    ∀ (s : ℕ) (b : ℕ → ℕ), (∀ k, b k + 1 ≤ b (k + 1)) →
    ∃ P : ℕ → Finset (Box (Fin d)),
      P 0 = (level Q (s * b 0)).boxes ∧
      boxUnion (P 0) = (Q : Set (Fin d → ℝ)) ∧
      (∀ k R, R ∈ P k → R ∈ D.cubes ((s * b k : ℕ) : ℤ)) ∧
      (∀ k, Set.PairwiseDisjoint (↑(P k) : Set (Box (Fin d)))
        (fun R => (R : Set (Fin d → ℝ)))) ∧
      (∀ k, boxUnion (P (k + 1)) ⊆ boxUnion (P k)) ∧
      (∀ k, MeasurableSet (boxUnion (P k)) ∧ volume (boxUnion (P k)) < ⊤) ∧
      (∀ k, volume.real (boxUnion (P k)) =
        ((2 : ℝ) ^ (-(s : ℤ))) ^ k * volume.real (Q : Set (Fin d → ℝ))) ∧
      (∀ k (n : ℤ), n ≤ ((s * (b (k + 1) - 1) : ℕ) : ℤ) → ∀ I ∈ D.cubes n,
        volume.real ((I : Set (Fin d → ℝ)) ∩ boxUnion (P (k + 1))) =
          (2 : ℝ) ^ (-(s : ℤ)) *
            volume.real ((I : Set (Fin d → ℝ)) ∩ boxUnion (P k)))

end ReyZygmundVerification
