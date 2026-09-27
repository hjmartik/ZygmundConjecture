import ReyZygmund.Continuous.RoundedEndpoint
import ReyZygmund.Geometry.ShiftedGrid

/-! # The rounded dyadic endpoint estimate

The rounded theorem is the prescribed-shift specialization of the arbitrary-grid
endpoint estimate. The passage to arbitrary side lengths is proved in
`Continuous/Endpoint.lean`. -/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal

namespace ReyZygmund.Main

open Geometry

/-- The paper's rounded endpoint, with the constant chosen before the
dimension vector, side function, shift, locally integrable input and level. -/
theorem rounded_endpoint_theorem :
  ∀ (n totalDim : ℕ), 2 ≤ n →
  ∃ C : ℝ, 0 < C ∧
  ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
  ∀ (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)), Monotone phi →
  ∀ (tau : ∀ i, Fin (d i) → Fin 3),
  ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
  ∀ (lam : ℝ), 0 < lam →
    volume {x | ENNReal.ofReal lam < euclideanFamilyMaximal
      (roundedGridRectangles (fun i => shiftedDyadicGrid (d i) (tau i)) phi) f x} ≤
    ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
      (|f x| / lam * (Real.log (Real.exp 1 + |f x| / lam)) ^ ((n + 1) - 2)) := by
  intro n totalDim hn
  obtain ⟨C, hC, hbound⟩ :=
    ReyZygmund.Continuous.rounded_grid_endpoint_theorem n totalDim hn
  refine ⟨C, hC, ?_⟩
  intro d hd hsum phi hphi tau f hf lam hlam
  simpa only [show n + 1 - 2 = n - 1 by omega] using
    hbound d hd hsum (fun i => shiftedDyadicGrid (d i) (tau i)) phi hphi f hf lam hlam

end ReyZygmund.Main
