import ReyZygmund.MathlibOnly.Definitions
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Independent statements of the three main results

`Definitions.lean` supplies the geometric objects, families and operators.
These statements and definitions form an independent specification.

`eLpNorm` denotes the extended `L^p` norm and `MemLp` membership in `L^p`;
`LocallyIntegrable` means membership in `L¹_loc`. The
[definition guide](DEFINITIONS.md#maximal-and-overlap-functions) explains
the integral and measurability conventions.

`Monotone` on tuples uses the coordinatewise order. `totalDim` is the sum
of the block dimensions.

For a prescribed last side length, `n` counts the independent side lengths,
so the number of cube factors is `m = n + 1`. The endpoint logarithmic power
is `n - 1 = m - 2`, and the overlap exponential power is `1 / n = 1 / (m - 1)`.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Classical Topology

namespace ReyZygmund.MathlibOnly

noncomputable section

/-- Weakly incomparable maximal estimate for `1 < p ≤ 2`.
The constant `C` depends only on the number of factors and total dimension.
Here `p / (p - 1)` is the conjugate exponent `p'`. -/
def WeaklyIncomparableMaximalEstimate : Prop :=
  ∀ (m totalDim : ℕ), 2 ≤ m → ∃ C : ℝ, 0 < C ∧
    ∀ (d : Fin m → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
      ∀ (grids : ∀ i, CubeGrid (d i)) (G : Set (Rectangle d)),
        G ⊆ gridRectangles grids → WeaklyIncomparable G →
        ∀ (p : ℝ), 1 < p → p ≤ 2 →
          ∀ (f : Point d → ℝ), MemLp f (ENNReal.ofReal p) volume →
            eLpNorm (maximal G f) (ENNReal.ofReal p) volume ≤
              ENNReal.ofReal (C * (p / (p - 1)) ^ (m - 1)) *
                eLpNorm f (ENNReal.ofReal p) volume

/-- Moments for `q ≥ 2` and exponential integrability of sparse weakly
incomparable families. The exponential estimate gives Rey's conjecture
under weak incomparability. -/
def WeaklyIncomparableReyConjecture : Prop :=
  ∀ (m totalDim : ℕ), 2 ≤ m → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (d : Fin m → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
      ∀ (grids : ∀ i, CubeGrid (d i)) (G : Set (Rectangle d)),
        G ⊆ gridRectangles grids → WeaklyIncomparable G →
        ∀ (eta : ℝ), 0 < eta → eta ≤ 1 → Sparse eta G → volume (shadow G) < ∞ →
          (∀ (q : ℝ), 2 ≤ q →
            eLpNorm (overlap G) (ENNReal.ofReal q) volume ≤
              ENNReal.ofReal (C * eta⁻¹ * q ^ (m - 1)) *
                (volume (shadow G)) ^ (1 / q)) ∧
          (∫⁻ x in shadow G, exp
            (ENNReal.ofReal c *
              (ENNReal.ofReal eta * overlap G x) ^ (1 / ((m - 1 : ℕ) : ℝ)))
              ∂volume) ≤ ENNReal.ofReal C * volume (shadow G)

/-- Zygmund's conjecture for a monotone prescribed last side length:
the continuous `L(log L)^(n-1)` endpoint estimate.
The constant depends only on the number of factors and total dimension. -/
def ZygmundConjecture : Prop :=
  ∀ (n totalDim : ℕ), 2 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
      ∀ (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)), Monotone phi →
        ∀ (f : Point d → ℝ), LocallyIntegrable f volume →
          ∀ (lam : ℝ), 0 < lam →
            volume {x | ENNReal.ofReal lam < maximal (zygmundRectangles d phi) f x} ≤
              ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
                (|f x| / lam * (Real.log (Real.exp 1 + |f x| / lam)) ^ (n - 1))
                  ∂volume

end
end ReyZygmund.MathlibOnly
