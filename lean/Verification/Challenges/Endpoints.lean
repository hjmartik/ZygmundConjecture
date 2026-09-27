import ReyZygmund.Geometry.PhiRectangles
import ReyZygmund.Geometry.RoundedScales
import ReyZygmund.Geometry.ShiftedGrid
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Independently stated endpoint estimates

The imports define rectangles, rounded scale images and shifted grids, without
importing the endpoint proofs or maximal estimates.

We define the supremum of supported averages of `|f|` separately from the proof
library's maximal operator. The statements assume local integrability when using
real rectangle integrals. Suprema and the right-hand logarithmic integrals are
extended-valued and may be infinite. Cubes use `(lower, upper]`.



-/

open BoxIntegral MeasureTheory ReyZygmund.Geometry
open scoped BigOperators ENNReal Classical

namespace ReyZygmundVerification.Challenges

noncomputable section

/-- The supported-average maximal function on ordinary Euclidean
coordinates. No finiteness, measurability or estimate is built into it. -/
def endpointMaximal {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ)
    (x : Fin (∑ i, d i) → ℝ) : ℝ≥0∞ :=
  ⨆ Q : G, ENNReal.ofReal
    ((flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)).indicator
      (fun _ => (∫ y in (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)),
        |f y| ∂volume) /
        volume.real (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ))) x)

/-- The continuous Zygmund estimate, with a constant depending only on the number of
parameters and total dimension, uniformly in the side function and input. -/
def continuousEndpointStatement : Prop :=
  ∀ (n totalDim : ℕ), 2 ≤ n →
  ∃ C : ℝ, 0 < C ∧
  ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
  ∀ (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)), Monotone phi →
  ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
  ∀ (lam : ℝ), 0 < lam →
    volume {x | ENNReal.ofReal lam <
      endpointMaximal (continuousPhiRectangles d phi) f x} ≤
    ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
      (|f x| / lam * (Real.log (Real.exp 1 + |f x| / lam)) ^ ((n + 1) - 2)) ∂volume

/-- The rounded endpoint estimate on the alternating shifted grids, with a constant
uniform in the shift tuple. -/
def roundedEndpointStatement : Prop :=
  ∀ (n totalDim : ℕ), 2 ≤ n →
  ∃ C : ℝ, 0 < C ∧
  ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
  ∀ (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)), Monotone phi →
  ∀ (tau : ∀ i, Fin (d i) → Fin 3),
  ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
  ∀ (lam : ℝ), 0 < lam →
    volume {x | ENNReal.ofReal lam < endpointMaximal
      (roundedGridRectangles (fun i => shiftedDyadicGrid (d i) (tau i)) phi) f x} ≤
    ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
      (|f x| / lam * (Real.log (Real.exp 1 + |f x| / lam)) ^ ((n + 1) - 2)) ∂volume

end

end ReyZygmundVerification.Challenges
