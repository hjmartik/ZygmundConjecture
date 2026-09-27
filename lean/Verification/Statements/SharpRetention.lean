import ReyZygmund.Sharpness.Retention

/-! Expected propositions for one concrete source retention step. -/

open BoxIntegral MeasureTheory
open scoped Classical

namespace ReyZygmundVerification

open ReyZygmund.Geometry

def sharpLevelVolumeContract : Prop :=
  ∀ {d s : ℕ} {Q R : Box (Fin d)}, R ∈ level Q s →
    volume.real (R : Set (Fin d → ℝ)) =
      volume.real (Q : Set (Fin d → ℝ)) / (2 : ℝ) ^ (s * d)

def sharpLevelCardContract : Prop :=
  ∀ {d : ℕ} (Q : Box (Fin d)) (s : ℕ), (level Q s).boxes.card = 2 ^ (s * d)

def sharpOneStepRetentionContract : Prop :=
  ∀ {d : ℕ}, 0 < d → ∀ (Q : Box (Fin d)) (s : ℕ),
    ∃ F : Finset (Box (Fin d)),
      F ⊆ (level Q s).boxes ∧
      F.card = 2 ^ (s * (d - 1)) ∧
      Set.PairwiseDisjoint (↑F : Set (Box (Fin d))) (fun R => (R : Set (Fin d → ℝ))) ∧
      (⋃ R ∈ F, (R : Set (Fin d → ℝ))) ⊆ (Q : Set (Fin d → ℝ)) ∧
      MeasurableSet (⋃ R ∈ F, (R : Set (Fin d → ℝ))) ∧
      0 < volume.real (⋃ R ∈ F, (R : Set (Fin d → ℝ))) ∧
      volume (⋃ R ∈ F, (R : Set (Fin d → ℝ))) < ⊤ ∧
      volume.real (⋃ R ∈ F, (R : Set (Fin d → ℝ))) =
        (2 : ℝ) ^ (-(s : ℤ)) * volume.real (Q : Set (Fin d → ℝ))

end ReyZygmundVerification
