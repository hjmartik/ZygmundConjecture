import ReyZygmund.Geometry.FiniteAverages
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
The exact finite one-coordinate weighted square statement. The scalar quotient
and coefficient are expanded independently of the candidate proof module.
-/

open BoxIntegral MeasureTheory ReyZygmund.Geometry
open scoped BigOperators Classical

namespace ReyZygmundVerification

noncomputable def weightedSquareContract : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (I : Box (Fin d)) (N : ℕ)
    (u v : (Fin d → ℝ) → ℝ) (p : ℝ), 1 < p → p ≤ 2 →
    (∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, u x = u y) →
    (∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, v x = v y) →
    (∀ x ∈ I, 0 < v x) →
    (∑ Q ∈ interior I N,
      ∫ x in (Q : Set (Fin d → ℝ)), (boxDifference Q u x) ^ 2 /
        Real.rpow ((∫ y in (Q : Set (Fin d → ℝ)), v y) /
          volume.real (Q : Set (Fin d → ℝ))) (2 - p)) ≤
      Real.rpow 2 ((d : ℝ) * (2 - p)) * ((3 - p) / (p - 1)) *
        ∫ x in (I : Set (Fin d → ℝ)), (u x) ^ 2 / Real.rpow (v x) (2 - p)

end ReyZygmundVerification
