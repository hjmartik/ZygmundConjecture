import ReyZygmund.Continuous.Endpoint
import ReyZygmund.Continuous.DyadicExtension

/-! # The original dyadic endpoint consequence

The integer-scale family is contained in the all-position continuous
family for the explicitly constructed extension. No restriction on the given
grids or on the finite/infinite family is introduced by this passage.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal

namespace ReyZygmund.Continuous

open Geometry

/-- The weak endpoint for every supplied grid and monotone integer side
relation. The constant is chosen before both, and before the input. -/
theorem dyadic_phi_endpoint_theorem :
    ∀ (n totalDim : ℕ), 2 ≤ n →
    ∃ C : ℝ, 0 < C ∧
    ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
    ∀ (D : ∀ i, DyadicGrid (d i)) (Phi : (Fin n → ℤ) → ℤ), Monotone Phi →
    ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    ∀ (lam : ℝ), 0 < lam →
      volume {x | ENNReal.ofReal lam <
        euclideanFamilyMaximal (dyadicPhiRectangles D Phi) f x} ≤
      ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
        (|f x| / lam * (Real.log (Real.exp 1 + |f x| / lam)) ^ ((n + 1) - 2)) := by
  intro n totalDim hn
  obtain ⟨C, hC, hbound⟩ := continuous_endpoint_theorem n totalDim hn
  refine ⟨C, hC, ?_⟩
  intro d hd hsum D Phi hPhi f hf lam hlam
  apply le_trans (measure_mono ?_)
    (hbound d hd hsum (dyadicPhiExtension Phi) (dyadicPhiExtension_mono Phi hPhi)
      f hf lam hlam)
  intro x hx
  exact hx.trans_le (dyadic_maximal_le_continuous D Phi f x)

end ReyZygmund.Continuous
