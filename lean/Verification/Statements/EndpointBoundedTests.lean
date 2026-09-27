import ReyZygmund.Maximal.Euclidean
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Bounded-test extension contract for the finite rectangle
maximal function. This module does not import the candidate proof. -/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry

def finiteEndpointOfBoundedTestsContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i))))
    (k : ℕ) (A : ℝ) (_hA : 0 ≤ A),
    (∀ h : (Fin (∑ i, d i) → ℝ) → ℝ,
      Measurable h → (∀ x, 0 ≤ h x) → (∃ B : ℝ, ∀ x, h x ≤ B) →
      Bornology.IsBounded (Function.support h) → ∀ t : ℝ, 0 < t →
      volume {x | ENNReal.ofReal t < euclideanFamilyMaximal (G : Set _) h x} ≤
        ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
          (|h x| / t * (Real.log (Real.exp 1 + |h x| / t)) ^ k)) →
    ∀ g : (Fin (∑ i, d i) → ℝ) → ℝ,
      LocallyIntegrable g volume → ∀ t : ℝ, 0 < t →
      volume {x | ENNReal.ofReal t < euclideanFamilyMaximal (G : Set _) g x} ≤
        ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
          (|g x| / t * (Real.log (Real.exp 1 + |g x| / t)) ^ k)

end ReyZygmundVerification
