import ReyZygmund.Geometry.FiniteAverages
import ReyZygmund.Maximal.FiniteOrdinary

/-! Explicit routine statement contracts for two finite analytic estimates. -/

open BoxIntegral MeasureTheory ReyZygmund.Geometry
open scoped BigOperators Classical

namespace ReyZygmundVerification

noncomputable def weightedAveragingContract : Prop :=
  ∀ {d : ℕ} (I : Box (Fin d)) (N : ℕ) (u v : (Fin d → ℝ) → ℝ) (p : ℝ),
    1 < p → p ≤ 2 →
    (∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, u x = u y) →
    (∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, v x = v y) →
    (∀ x ∈ I, 0 < v x) →
    (((∫ x in (I : Set (Fin d → ℝ)), u x) /
        volume.real (I : Set (Fin d → ℝ))) ^ (2 : ℕ)) /
      Real.rpow ((∫ x in (I : Set (Fin d → ℝ)), v x) /
        volume.real (I : Set (Fin d → ℝ))) (2 - p) ≤
      (∫ x in (I : Set (Fin d → ℝ)), (u x) ^ (2 : ℕ) / Real.rpow (v x) (2 - p)) /
        volume.real (I : Set (Fin d → ℝ))

noncomputable def finiteOrdinaryMaximalContract : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (I : Box (Fin d)) (N : ℕ) (g : (Fin d → ℝ) → ℝ)
    (p : ℝ), 1 < p →
    (∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y) →
    Real.rpow
      (∫ x in (I : Set (Fin d → ℝ)), Real.rpow (ReyZygmund.finiteDyadicMaximal I N g x) p)
      (1 / p) ≤
      (p / (p - 1)) * Real.rpow
        (∫ x in (I : Set (Fin d → ℝ)), Real.rpow |g x| p) (1 / p)

end ReyZygmundVerification
