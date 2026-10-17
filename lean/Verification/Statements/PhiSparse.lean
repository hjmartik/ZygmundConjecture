import Verification.Statements.MainOverlap

/-! # Sparse Phi-Zygmund estimates in real-valued form

The shared definitions supply the grids, prescribed side-length family and
overlap. The two propositions express exponential integrability and sharpness
using the overlap's real-valued representative.

-/

open BoxIntegral MeasureTheory Filter
open scoped BigOperators ENNReal Classical Topology

open ReyZygmund.MathlibOnly (dyadicZygmundRectangles rectangle shadow overlap)

namespace ReyZygmundVerification

noncomputable section

/-- The sparse Phi-Zygmund overlap estimate, with `n = m - 1`. Both positive constants are
chosen before the dimension vector, grids, monotone side relation and sparse
family. No incomparability is required. AE finiteness precedes use of
the overlap's real representative. -/
def phiSparseOverlapStatement : Prop :=
  ∀ (n totalDim : ℕ), 2 ≤ n →
    ∀ (eta : ℝ), 0 < eta → eta ≤ 1 →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
          ∀ (D : ∀ i, ReyZygmund.MathlibOnly.CubeGrid (d i))
            (Phi : (Fin n → ℤ) → ℤ), Monotone Phi →
            ∀ (G : Set (∀ i, Box (Fin (d i)))),
              G ⊆ dyadicZygmundRectangles D Phi → ReyZygmund.MathlibOnly.Sparse eta G → volume (shadow G) < ∞ →
                (∀ᵐ x ∂volume, overlap G x < ∞) ∧
                  (∫⁻ x in shadow G, ENNReal.ofReal
                    (Real.exp (c * Real.rpow (overlap G x).toReal (1 / (n : ℝ)))) - 1
                      ∂volume) ≤ ENNReal.ofReal C * volume (shadow G)

/-- The sharpness statement for the classical sum relation. One sequence of finite
families works for every `c > 0` and `beta > 1/n`; for each `N ≥ 2` the family is
incomparable, sparse and has unit shadow. The nonnegative exponential integrals
diverge to infinity. -/
def phiSparseSharpnessStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) →
      ∀ (D : ∀ i, ReyZygmund.MathlibOnly.CubeGrid (d i))
        (eta : ℝ), 0 < eta → eta < 1 →
        ∃ G : ℕ → Finset (∀ i, Box (Fin (d i))),
          (∀ N : ℕ, 2 ≤ N →
            (G N : Set (∀ i, Box (Fin (d i)))) ⊆
                dyadicZygmundRectangles D (fun k : Fin n → ℤ => ∑ i, k i) ∧
              (∀ R ∈ G N, ∀ S ∈ G N, rectangle R ⊆ rectangle S → R = S) ∧
              ReyZygmund.MathlibOnly.Sparse eta (G N : Set (∀ i, Box (Fin (d i)))) ∧
              volume (shadow (G N : Set (∀ i, Box (Fin (d i))))) = 1) ∧
          ∀ (c beta : ℝ), 0 < c → 1 / (n : ℝ) < beta →
            Tendsto (fun N : ℕ =>
              ∫⁻ x in shadow (G N : Set (∀ i, Box (Fin (d i)))),
                ENNReal.ofReal (Real.exp (c * Real.rpow
                  (overlap (G N : Set (∀ i, Box (Fin (d i)))) x).toReal beta)) - 1
                    ∂volume) atTop (𝓝 ∞)

end

end ReyZygmundVerification
