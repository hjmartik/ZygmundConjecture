import ReyZygmund.MathlibOnly.Proof.EstimateDefinitions
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Supporting forms of the six main estimates

The public proofs use these estimates to establish the independent statements
in `ReyZygmund.MathlibOnly.Statements`, including the sharpness result.

The `L^p` maximal estimate is stated for `1 < p ≤ 2`. This estimate and the sparse
overlap statements include almost-everywhere finiteness, so their real-valued
versions agree with the extended quantities outside a set of measure zero.

-/

open BoxIntegral MeasureTheory Filter
open scoped BigOperators ENNReal Classical Topology

namespace ReyZygmund.MathlibOnly.Proof.Estimates

noncomputable section

/-- Weakly incomparable maximal estimate: no sparsity or finite-shadow assumption. -/
def WeaklyIncomparableMaximal : Prop :=
  ∃ C : ℕ → ℕ → ℝ, (∀ m D, 0 < C m D) ∧
    ∀ (m : ℕ) (d : Fin m → ℕ), 2 ≤ m → (∀ i, 0 < d i) →
      ∀ (D : ∀ i, CubeGrid (d i)) (G : Set (∀ i, Box (Fin (d i)))),
        G ⊆ gridRectangles D → WeaklyIncomparable G →
        ∀ (p : ℝ), 1 < p → p ≤ 2 →
          ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ), MemLp f (ENNReal.ofReal p) volume →
            (∀ᵐ x ∂volume, maximal G f x < ∞) ∧
              eLpNorm (fun x => (maximal G f x).toReal) (ENNReal.ofReal p) volume ≤
                ENNReal.ofReal (C m (∑ i, d i) * (p / (p - 1)) ^ (m - 1)) *
                  eLpNorm f (ENNReal.ofReal p) volume

/-- Moments and exponential overlap under weak
incomparability, with constants uniform in the sparsity parameter. -/
def WeaklyIncomparableOverlap : Prop :=
  ∃ C c : ℕ → ℕ → ℝ, (∀ m D, 0 < C m D) ∧ (∀ m D, 0 < c m D) ∧
    ∀ (m : ℕ) (d : Fin m → ℕ), 2 ≤ m → (∀ i, 0 < d i) →
      ∀ (D : ∀ i, CubeGrid (d i)) (G : Set (∀ i, Box (Fin (d i)))),
        G ⊆ gridRectangles D → WeaklyIncomparable G →
        ∀ (eta : ℝ), 0 < eta → eta ≤ 1 → Sparse eta G → volume (shadow G) < ∞ →
          (∀ᵐ x ∂volume, overlap G x < ∞) ∧
          (∀ (q : ℝ), 2 ≤ q →
            eLpNorm (fun x => (overlap G x).toReal) (ENNReal.ofReal q) volume ≤
              ENNReal.ofReal (C m (∑ i, d i) * eta⁻¹ * q ^ (m - 1)) *
                (volume (shadow G)) ^ (1 / q)) ∧
          (∫⁻ x in shadow G, ENNReal.ofReal
            (Real.exp (c m (∑ i, d i) *
              Real.rpow (eta * (overlap G x).toReal) (1 / ((m - 1 : ℕ) : ℝ))))
              ∂volume) ≤ ENNReal.ofReal (C m (∑ i, d i)) * volume (shadow G)

/-- Continuous Zygmund endpoint estimate, with `n = m - 1`. -/
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

/-- Dyadic endpoint estimate for the complete rounded image in each
prescribed shifted grid, with constants independent of the shift. -/
def RoundedEndpoint : Prop :=
  ∀ (n totalDim : ℕ), 2 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
      ∀ (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)), Monotone phi →
        ∀ (tau : ∀ i, Fin (d i) → Fin 3),
          ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
            ∀ (lam : ℝ), 0 < lam →
              volume {x | ENNReal.ofReal lam < maximalIco (roundedRectangles tau phi) f x} ≤
                ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
                  (|f x| / lam * (Real.log (Real.exp 1 + |f x| / lam)) ^ ((n + 1) - 2))
                    ∂volume

/-- Sparse prescribed-scale overlap, without an incomparability hypothesis. -/
def PhiSparseOverlap : Prop :=
  ∀ (n totalDim : ℕ), 2 ≤ n → ∀ (eta : ℝ), 0 < eta → eta ≤ 1 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
        ∀ (D : ∀ i, CubeGrid (d i)) (Phi : (Fin n → ℤ) → ℤ), Monotone Phi →
          ∀ (G : Set (∀ i, Box (Fin (d i)))),
            G ⊆ phiRectangles D Phi → Sparse eta G → volume (shadow G) < ∞ →
              (∀ᵐ x ∂volume, overlap G x < ∞) ∧
                (∫⁻ x in shadow G, ENNReal.ofReal
                  (Real.exp (c * Real.rpow (overlap G x).toReal (1 / (n : ℝ))))
                    ∂volume) ≤ ENNReal.ofReal C * volume (shadow G)

/-- Sharpness for sparse incomparable classical Zygmund families.
One unit-shadow sequence works for every larger power and positive coefficient. -/
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
            ∫ x in shadow (G N : Set (∀ i, Box (Fin (d i)))),
              Real.exp (c * Real.rpow
                (overlap (G N : Set (∀ i, Box (Fin (d i)))) x).toReal beta)
                  ∂volume) atTop atTop

end
end ReyZygmund.MathlibOnly.Proof.Estimates
