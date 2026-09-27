import ReyZygmund.Sharpness.RetainedPartition

/-! Expected statements for finite refinement and one retention step. -/

open BoxIntegral MeasureTheory
open scoped Classical

namespace ReyZygmundVerification

open ReyZygmund.Geometry ReyZygmund.Sharpness

def sharpRefinementUnionContract : Prop :=
  ∀ {d : ℕ} (P : Finset (Box (Fin d))) (t : ℕ),
    boxUnion (P.biUnion (fun Q => (level Q t).boxes)) = boxUnion P

def sharpRetainedPartitionContract : Prop :=
  ∀ {d : ℕ}, 0 < d → ∀ (D : DyadicGrid d) (n : ℤ) (P : Finset (Box (Fin d))),
    (∀ Q ∈ P, Q ∈ D.cubes n) → ∀ s : ℕ,
    ∃ F : Finset (Box (Fin d)),
      F ⊆ P.biUnion (fun Q => (level Q s).boxes) ∧
      (∀ R ∈ F, R ∈ D.cubes (n + (s : ℤ))) ∧
      Set.PairwiseDisjoint (↑F : Set (Box (Fin d))) (fun R => (R : Set (Fin d → ℝ))) ∧
      boxUnion F ⊆ boxUnion P ∧
      MeasurableSet (boxUnion F) ∧
      volume (boxUnion F) < ⊤ ∧
      volume.real (boxUnion F) = (2 : ℝ) ^ (-(s : ℤ)) * volume.real (boxUnion P) ∧
      ∀ (k : ℤ), k ≤ n → ∀ I ∈ D.cubes k,
        volume.real ((I : Set (Fin d → ℝ)) ∩ boxUnion F) =
          (2 : ℝ) ^ (-(s : ℤ)) *
            volume.real ((I : Set (Fin d → ℝ)) ∩ boxUnion P)

end ReyZygmundVerification
