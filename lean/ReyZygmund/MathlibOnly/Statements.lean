import ReyZygmund.MathlibOnly.Definitions
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Independent statements of the six main results

The definitions needed to read these statements are in `Definitions.lean`.
Neither file imports the proof library.

`eLpNorm` denotes the `L^p` norm, allowing the value infinity; `MemLp` means
membership in `L^p`. `LocallyIntegrable` means membership in `L¹_loc`.
`Monotone` on tuples uses the coordinatewise order.

`totalDim` is the sum of the block dimensions. Choosing the constants before
the dimension vector `d` makes the estimates uniform over all splits of that sum.

For a prescribed last side length, `n` counts the independent side lengths,
so the number of cube factors is `m = n + 1`. The logarithmic endpoint power
is `n - 1 = m - 2`, and the overlap exponential power is `1 / n = 1 / (m - 1)`.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Classical Topology

namespace ReyZygmund.MathlibOnly

noncomputable section

/-- Weakly incomparable maximal estimate for `1 < p ≤ 2`.
The constant depends only on the number of factors and total dimension.
Here `p / (p - 1)` is the conjugate exponent `p'`. -/
def WeaklyIncomparableMaximal : Prop :=
  ∀ (m totalDim : ℕ), 2 ≤ m → ∃ C : ℝ, 0 < C ∧
    ∀ (d : Fin m → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
      ∀ (grids : ∀ i, CubeGrid (d i)) (G : Set (Rectangle d)),
        G ⊆ gridRectangles grids → WeaklyIncomparable G →
        ∀ (p : ℝ), 1 < p → p ≤ 2 →
          ∀ (f : Point d → ℝ), MemLp f (ENNReal.ofReal p) volume →
            eLpNorm (maximal G f) (ENNReal.ofReal p) volume ≤
              ENNReal.ofReal (C * (p / (p - 1)) ^ (m - 1)) *
                eLpNorm f (ENNReal.ofReal p) volume

/-- Moments and exponential overlap for sparse weakly incomparable families.
Both constants depend only on the number of factors and total dimension,
uniformly for `0 < eta ≤ 1`. -/
def WeaklyIncomparableOverlap : Prop :=
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

/-- The continuous Zygmund `L(log L)^(n-1)` endpoint estimate.
The constant depends only on the number of factors and total dimension. -/
def ContinuousEndpoint : Prop :=
  ∀ (n totalDim : ℕ), 2 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
      ∀ (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)), Monotone phi →
        ∀ (f : Point d → ℝ), LocallyIntegrable f volume →
          ∀ (lam : ℝ), 0 < lam →
            volume {x | ENNReal.ofReal lam < maximal (continuousRectangles d phi) f x} ≤
              ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
                (|f x| / lam * (Real.log (Real.exp 1 + |f x| / lam)) ^ (n - 1))
                  ∂volume

/-- The rounded dyadic endpoint estimate in each prescribed shifted grid.
The constant depends only on the number of factors and total dimension,
uniformly in `phi` and `tau`. -/
def RoundedEndpoint : Prop :=
  ∀ (n totalDim : ℕ), 2 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
      ∀ (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)), Monotone phi →
        ∀ (tau : ∀ i, Fin (d i) → Fin 3),
          ∀ (f : Point d → ℝ), LocallyIntegrable f volume →
            ∀ (lam : ℝ), 0 < lam →
              volume {x | ENNReal.ofReal lam < maximalIco (roundedRectangles tau phi) f x} ≤
                ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
                  (|f x| / lam * (Real.log (Real.exp 1 + |f x| / lam)) ^ (n - 1))
                    ∂volume

/-- Sparse Φ-Zygmund exponential overlap.
The constants depend only on the number of factors, total dimension and `eta`. -/
def PhiSparseOverlap : Prop :=
  ∀ (n totalDim : ℕ), 2 ≤ n → ∀ (eta : ℝ), 0 < eta → eta ≤ 1 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
        ∀ (grids : ∀ i, CubeGrid (d i)) (Phi : (Fin n → ℤ) → ℤ), Monotone Phi →
          ∀ (G : Set (Rectangle d)),
            G ⊆ phiRectangles grids Phi → Sparse eta G → volume (shadow G) < ∞ →
              (∫⁻ x in shadow G,
                exp (ENNReal.ofReal c * overlap G x ^ (1 / (n : ℝ))) ∂volume) ≤
                  ENNReal.ofReal C * volume (shadow G)

/-- Sharpness for the classical dyadic Zygmund family, with `Phi k = ∑ i, k i`.
For every choice of grids and `0 < eta < 1`, one sequence of finite incomparable
sparse families has shadows of measure one and divergent exponential integrals
for every positive coefficient and every power above `1 / n`.
The real indicator sum is the overlap of the finite family. It is measurable
and bounded, so its exponential has a finite real integral on the shadow. -/
def PhiSparseSharpness : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) →
    ∀ (grids : ∀ i, CubeGrid (d i)) (eta : ℝ), 0 < eta → eta < 1 →
      ∃ G : ℕ → Finset (Rectangle d),
        (∀ N : ℕ, 2 ≤ N →
          (G N : Set (Rectangle d)) ⊆
              phiRectangles grids (fun k : Fin n → ℤ => ∑ i, k i) ∧
            Incomparable (G N : Set (Rectangle d)) ∧
            Sparse eta (G N : Set (Rectangle d)) ∧
            volume (shadow (G N : Set (Rectangle d))) = 1) ∧
        ∀ (c beta : ℝ), 0 < c → 1 / (n : ℝ) < beta →
          Tendsto (fun N : ℕ =>
            ∫ x in shadow (G N : Set (Rectangle d)),
              Real.exp (c * Real.rpow
                (∑ R ∈ G N, (rectangle R).indicator (fun _ => (1 : ℝ)) x) beta)
                  ∂volume) atTop atTop

end
end ReyZygmund.MathlibOnly
