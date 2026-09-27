import ReyZygmund.Continuous.DyadicExtension
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Explicit source proposition for the dyadic endpoint consequence. -/

open BoxIntegral MeasureTheory ReyZygmund ReyZygmund.Geometry
open scoped BigOperators ENNReal

namespace ReyZygmundVerification

def dyadicPhiEndpointContract : Prop :=
  ∀ (n totalDim : ℕ), 2 ≤ n →
  ∃ C : ℝ, 0 < C ∧
  ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
  ∀ (D : ∀ i, DyadicGrid (d i)) (Phi : (Fin n → ℤ) → ℤ), Monotone Phi →
  ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
  ∀ (lam : ℝ), 0 < lam →
    volume {x | ENNReal.ofReal lam <
      euclideanFamilyMaximal (Continuous.dyadicPhiRectangles D Phi) f x} ≤
    ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
      (|f x| / lam * (Real.log (Real.exp 1 + |f x| / lam)) ^ ((n + 1) - 2)) ∂volume

end ReyZygmundVerification
