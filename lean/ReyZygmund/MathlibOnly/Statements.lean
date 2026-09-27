import ReyZygmund.MathlibOnly.Definitions
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Seven independently stated results

The only local import is the Mathlib-only definition file. This file defines
propositions; their proofs are in separate modules importing the proof library.

The order of quantifiers specifies the allowed dependence of each constant.
Real-valued representatives of maximal functions and overlaps are accompanied by
almost-everywhere finiteness conclusions.


-/

open BoxIntegral MeasureTheory Filter
open scoped BigOperators ENNReal Classical Topology

namespace ReyZygmund.MathlibOnly

noncomputable section

/-- Incomparable maximal estimate. The range `1 < p` includes the paper's
stated range `1 < p ≤ 2`. -/
def IncomparableMaximal : Prop :=
  ∃ C : ℕ → ℕ → ℝ, (∀ m D, 0 < C m D) ∧
    ∀ (m : ℕ) (d : Fin m → ℕ), 2 ≤ m → (∀ i, 0 < d i) →
      ∀ (D : ∀ i, CubeGrid (d i)) (G : Set (∀ i, Box (Fin (d i)))),
        G ⊆ gridRectangles D → Incomparable G →
        ∀ (p : ℝ), 1 < p →
          ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ), MemLp f (ENNReal.ofReal p) volume →
            (∀ᵐ x ∂volume, maximal G f x < ∞) ∧
              eLpNorm (fun x => (maximal G f x).toReal) (ENNReal.ofReal p) volume ≤
                ENNReal.ofReal (C m (∑ i, d i) * (p / (p - 1)) ^ (m - 1)) *
                  eLpNorm f (ENNReal.ofReal p) volume

/-- Sparse incomparable overlap: every real moment `q ≥ 2`, and exponential
power `1/(m-1)`, with the sparsity parameter inside that power. -/
def IncomparableOverlap : Prop :=
  ∃ C c : ℕ → ℕ → ℝ, (∀ m D, 0 < C m D) ∧ (∀ m D, 0 < c m D) ∧
    ∀ (m : ℕ) (d : Fin m → ℕ), 2 ≤ m → (∀ i, 0 < d i) →
      ∀ (D : ∀ i, CubeGrid (d i)) (G : Set (∀ i, Box (Fin (d i)))),
        G ⊆ gridRectangles D → Incomparable G →
        ∀ (eta : ℝ), 0 < eta → eta ≤ 1 → Sparse eta G → volume (shadow G) < ∞ →
          (∀ᵐ x ∂volume, overlap G x < ∞) ∧
          (∀ (q : ℝ), 2 ≤ q →
            eLpNorm (fun x => (overlap G x).toReal) (ENNReal.ofReal q) volume ≤
              ENNReal.ofReal (C m (∑ i, d i) * eta⁻¹ * q ^ (m - 1)) *
                (volume (shadow G)) ^ (1 / q)) ∧
          (∫⁻ x in shadow G, ENNReal.ofReal
            (Real.exp (c m (∑ i, d i) *
              Real.rpow (eta * (overlap G x).toReal) (1 / ((m - 1 : ℕ) : ℝ))) - 1)
              ∂volume) ≤ ENNReal.ofReal (C m (∑ i, d i)) * volume (shadow G)

/-- The maximal estimate and both sparse conclusions when containment preserves
some cube factor. Sparsity and finite shadow restrict only the overlap part. -/
def WeakerContainment : Prop :=
  ∃ C c : ℕ → ℕ → ℝ, (∀ m D, 0 < C m D) ∧ (∀ m D, 0 < c m D) ∧
    ∀ (m : ℕ) (d : Fin m → ℕ), 2 ≤ m → (∀ i, 0 < d i) →
      ∀ (D : ∀ i, CubeGrid (d i)) (G : Set (∀ i, Box (Fin (d i)))),
        G ⊆ gridRectangles D → HasEqualFactorOnContainment G →
        (∀ (p : ℝ), 1 < p → p ≤ 2 →
          ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ), MemLp f (ENNReal.ofReal p) volume →
            (∀ᵐ x ∂volume, maximal G f x < ∞) ∧
              eLpNorm (fun x => (maximal G f x).toReal) (ENNReal.ofReal p) volume ≤
                ENNReal.ofReal (C m (∑ i, d i) * (p / (p - 1)) ^ (m - 1)) *
                  eLpNorm f (ENNReal.ofReal p) volume) ∧
        (∀ (eta : ℝ), 0 < eta → eta ≤ 1 → Sparse eta G → volume (shadow G) < ∞ →
          (∀ᵐ x ∂volume, overlap G x < ∞) ∧
          (∀ (q : ℝ), 2 ≤ q →
            eLpNorm (fun x => (overlap G x).toReal) (ENNReal.ofReal q) volume ≤
              ENNReal.ofReal (C m (∑ i, d i) * eta⁻¹ * q ^ (m - 1)) *
                (volume (shadow G)) ^ (1 / q)) ∧
          (∫⁻ x in shadow G, ENNReal.ofReal
            (Real.exp (c m (∑ i, d i) *
              Real.rpow (eta * (overlap G x).toReal) (1 / ((m - 1 : ℕ) : ℝ))) - 1)
              ∂volume) ≤ ENNReal.ofReal (C m (∑ i, d i)) * volume (shadow G))

/-- Continuous Zygmund endpoint for `n+1` blocks, with no hypothesis on the
positive side function other than coordinatewise monotonicity. -/
def ContinuousEndpoint : Prop :=
  ∀ (n totalDim : ℕ), 2 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
      ∀ (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)), Monotone phi →
        ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
          ∀ (lam : ℝ), 0 < lam →
            volume {x | ENNReal.ofReal lam < maximal (continuousRectangles d phi) f x} ≤
              ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
                (|f x| / lam * (Real.log (Real.exp 1 + |f x| / lam)) ^ ((n + 1) - 2))
                  ∂volume

/-- The same endpoint for each prescribed shifted grid and the full rounded
scale image, with the constant independent of both shift and side function. -/
def RoundedEndpoint : Prop :=
  ∀ (n totalDim : ℕ), 2 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
      ∀ (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)), Monotone phi →
        ∀ (tau : ∀ i, Fin (d i) → Fin 3),
          ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
            ∀ (lam : ℝ), 0 < lam →
              volume {x | ENNReal.ofReal lam < maximal (roundedRectangles tau phi) f x} ≤
                ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
                  (|f x| / lam * (Real.log (Real.exp 1 + |f x| / lam)) ^ ((n + 1) - 2))
                    ∂volume

/-- Sparse prescribed-scale overlap, without incomparability. Here `n=m-1`;
the constants can depend on sparsity but not on grids or the side relation. -/
def PhiSparseOverlap : Prop :=
  ∀ (n totalDim : ℕ), 2 ≤ n → ∀ (eta : ℝ), 0 < eta → eta ≤ 1 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
        ∀ (D : ∀ i, CubeGrid (d i)) (Phi : (Fin n → ℤ) → ℤ), Monotone Phi →
          ∀ (G : Set (∀ i, Box (Fin (d i)))),
            G ⊆ phiRectangles D Phi → Sparse eta G → volume (shadow G) < ∞ →
              (∀ᵐ x ∂volume, overlap G x < ∞) ∧
                (∫⁻ x in shadow G, ENNReal.ofReal
                  (Real.exp (c * Real.rpow (overlap G x).toReal (1 / (n : ℝ)))) - 1
                    ∂volume) ≤ ENNReal.ofReal C * volume (shadow G)

/-- Sharpness for the classical sum of side exponents. For every grid and
sparsity parameter, one sequence works for every larger power and positive
coefficient; each term from index two onward has unit shadow. -/
def PhiSparseSharpness : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) →
    ∀ (D : ∀ i, CubeGrid (d i)) (eta : ℝ), 0 < eta → eta < 1 →
      ∃ G : ℕ → Finset (∀ i, Box (Fin (d i))),
        (∀ N : ℕ, 2 ≤ N →
          (G N : Set (∀ i, Box (Fin (d i)))) ⊆
              phiRectangles D (fun k : Fin n → ℤ => ∑ i, k i) ∧
            Incomparable (G N : Set (∀ i, Box (Fin (d i)))) ∧
            Sparse eta (G N : Set (∀ i, Box (Fin (d i)))) ∧
            volume (shadow (G N : Set (∀ i, Box (Fin (d i))))) = 1) ∧
        ∀ (c beta : ℝ), 0 < c → 1 / (n : ℝ) < beta →
          Tendsto (fun N : ℕ =>
            ∫⁻ x in shadow (G N : Set (∀ i, Box (Fin (d i)))),
              ENNReal.ofReal (Real.exp (c * Real.rpow
                (overlap (G N : Set (∀ i, Box (Fin (d i)))) x).toReal beta)) - 1
                  ∂volume) atTop (𝓝 ∞)

end
end ReyZygmund.MathlibOnly
