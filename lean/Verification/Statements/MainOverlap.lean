import Verification.Statements.MainMaximal
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Maximal and overlap estimates in real-valued form

The shared definitions supply the rectangles, grids, maximal function and
overlap. Almost-everywhere finiteness accompanies estimates using their
real-valued representatives.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

open ReyZygmund.MathlibOnly (gridRectangles rectangle maximal shadow overlap)

namespace ReyZygmundVerification

noncomputable section

/-- The incomparable overlap estimate: dimension-only constants, all real
moments `q ≥ 2`, and the exponential estimate on the finite shadow. Almost-everywhere finiteness
is an explicit conclusion before either use of the real representative. -/
def incomparableOverlapStatement : Prop :=
  ∃ C c : ℕ → ℕ → ℝ,
    (∀ m D, 0 < C m D) ∧ (∀ m D, 0 < c m D) ∧
    ∀ (m : ℕ) (d : Fin m → ℕ), 2 ≤ m → (∀ i : Fin m, 0 < d i) →
      ∀ (D : ∀ i : Fin m, ReyZygmund.MathlibOnly.CubeGrid (d i))
        (G : Set (∀ i : Fin m, Box (Fin (d i)))),
        G ⊆ gridRectangles D →
        (∀ R ∈ G, ∀ S ∈ G, rectangle R ⊆ rectangle S → R = S) →
        ∀ (η : ℝ), 0 < η → η ≤ 1 → ReyZygmund.MathlibOnly.Sparse η G → volume (shadow G) < ∞ →
          (∀ᵐ x ∂volume, overlap G x < ∞) ∧
          (∀ (q : ℝ), 2 ≤ q →
            eLpNorm (fun x => (overlap G x).toReal) (ENNReal.ofReal q) volume ≤
              ENNReal.ofReal (C m (∑ i, d i) * η⁻¹ * q ^ (m - 1)) *
                (volume (shadow G)) ^ (1 / q)) ∧
          (∫⁻ x in shadow G, ENNReal.ofReal
            (Real.exp (c m (∑ i, d i) *
              Real.rpow (η * (overlap G x).toReal) (1 / ((m - 1 : ℕ) : ℝ))) - 1)
              ∂volume) ≤ ENNReal.ofReal (C m (∑ i, d i)) * volume (shadow G)

/-- Maximal and overlap estimates in the equal-factor form of weak incomparability.
The maximal estimate requires neither sparsity nor finite shadow; the overlap
conclusions have these additional hypotheses. -/
def weakerContainmentStatement : Prop :=
  ∃ C c : ℕ → ℕ → ℝ,
    (∀ m D, 0 < C m D) ∧ (∀ m D, 0 < c m D) ∧
    ∀ (m : ℕ) (d : Fin m → ℕ), 2 ≤ m → (∀ i : Fin m, 0 < d i) →
      ∀ (D : ∀ i : Fin m, ReyZygmund.MathlibOnly.CubeGrid (d i))
        (G : Set (∀ i : Fin m, Box (Fin (d i)))),
        G ⊆ gridRectangles D →
        (∀ R ∈ G, ∀ S ∈ G, rectangle R ⊆ rectangle S →
          ∃ i : Fin m, R i = S i) →
        ((∀ (p : ℝ), 1 < p → p ≤ 2 →
          ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ),
            MemLp f (ENNReal.ofReal p) volume →
            (∀ᵐ x ∂volume, maximal G f x < ∞) ∧
              eLpNorm (fun x => (maximal G f x).toReal)
                  (ENNReal.ofReal p) volume ≤
                ENNReal.ofReal (C m (∑ i, d i) * (p / (p - 1)) ^ (m - 1)) *
                  eLpNorm f (ENNReal.ofReal p) volume) ∧
        (∀ (η : ℝ), 0 < η → η ≤ 1 → ReyZygmund.MathlibOnly.Sparse η G → volume (shadow G) < ∞ →
          (∀ᵐ x ∂volume, overlap G x < ∞) ∧
          (∀ (q : ℝ), 2 ≤ q →
            eLpNorm (fun x => (overlap G x).toReal) (ENNReal.ofReal q) volume ≤
              ENNReal.ofReal (C m (∑ i, d i) * η⁻¹ * q ^ (m - 1)) *
                (volume (shadow G)) ^ (1 / q)) ∧
          (∫⁻ x in shadow G, ENNReal.ofReal
            (Real.exp (c m (∑ i, d i) *
              Real.rpow (η * (overlap G x).toReal) (1 / ((m - 1 : ℕ) : ℝ))) - 1)
              ∂volume) ≤ ENNReal.ofReal (C m (∑ i, d i)) * volume (shadow G)))

end

end ReyZygmundVerification
