import ReyZygmund.Geometry.FiniteAverages
import ReyZygmund.Geometry.FinitePartition

/-! # Finite geometric statements

These propositions use separately reviewed definitions, not the types or proofs of
the theorems being checked. The inspector compares elaborated statements by
definitional equality. Mathematical review separately checks their correspondence
with the paper.

-/

open BoxIntegral MeasureTheory ReyZygmund.Geometry
open scoped BigOperators Classical

namespace ReyZygmundVerification

noncomputable def finiteCubeRealizationContract : Prop :=
  ∀ (d : ℕ) (lower : Fin d → ℝ) (a : ℤ) (N : ℕ),
    (level (rootBox lower a) N).IsPartition ∧
    ∀ Q ∈ leaves (rootBox lower a) N,
      0 < volume.real (Q : Set (Fin d → ℝ)) ∧
      volume (Q : Set (Fin d → ℝ)) < ⊤ ∧
      (∀ i : Fin d, Q.upper i - Q.lower i = (2 : ℝ) ^ (a - (N : ℤ))) ∧
      (Prepartition.splitCenter Q).boxes.card = 2 ^ d

noncomputable def interiorCutoffContract : Prop :=
  ∀ {d : ℕ} (i : Fin d) {lower : Fin d → ℝ} {a : ℤ}
    {J : Box (Fin d)} {N : ℕ},
    J ∈ interior (rootBox lower a) N ↔
      J ∈ descendants (rootBox lower a) N ∧
        (2 : ℝ) ^ (a - (N : ℤ)) < J.upper i - J.lower i

noncomputable def leafCutoffContract : Prop :=
  ∀ {d : ℕ} (i : Fin d) {lower : Fin d → ℝ} {a : ℤ}
    {J : Box (Fin d)} {N : ℕ},
    J ∈ leaves (rootBox lower a) N ↔
      J ∈ descendants (rootBox lower a) N ∧
        J.upper i - J.lower i = (2 : ℝ) ^ (a - (N : ℤ))

noncomputable def leafConstantIntegrableContract : Prop :=
  ∀ {d : ℕ} (I : Box (Fin d)) (N : ℕ) (g : (Fin d → ℝ) → ℝ),
    (∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y) →
      IntegrableOn g (I : Set (Fin d → ℝ)) volume

noncomputable def oneCoordinateTelescopeContract : Prop :=
  ∀ (d : ℕ), 0 < d →
    ∀ (I : Box (Fin d)) (N : ℕ) (P : Box (Fin d)), P ∈ descendants I N →
      ∀ (g : (Fin d → ℝ) → ℝ),
        (∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y) →
        (∑ L ∈ (interior I N).filter (fun L => L ≤ P), boxDifference L g) =
          (∑ Q ∈ (leaves I N).filter (fun Q => Q ≤ P), boxAverage Q g) - boxAverage P g ∧
        (∑ Q ∈ (leaves I N).filter (fun Q => Q ≤ P), boxAverage Q g) - boxAverage P g =
          (P : Set (Fin d → ℝ)).indicator g - boxAverage P g

noncomputable def partitionIndicesContract : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (I : Box (Fin d)) (N : ℕ) (eligible : Finset (Box (Fin d))),
    (interior I N).filter (fun L => ∃ J ∈ eligible, L ≤ J) =
      (interior I N).filter (fun L => ∃ P ∈ partitionCubes I N eligible, L ≤ P)

noncomputable def maximalPartitionContract : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (I : Box (Fin d)) (N : ℕ) (eligible : Finset (Box (Fin d)))
    (he : eligible ⊆ descendants I N),
    (maximalPartition I N eligible he).IsPartition ∧
      ∀ L ∈ interior I N, (∃ J ∈ eligible, L ≤ J) →
        ∃! P, P ∈ partitionCubes I N eligible ∧ L ≤ P

end ReyZygmundVerification
