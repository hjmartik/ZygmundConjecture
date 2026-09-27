import Verification.Challenges.Maximal
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Independently stated overlap estimates

The maximal specification supplies the rectangles, grids and maximal operator
using averages of `|f|`. No overlap proof is imported. The overlap is an extended
nonnegative sum, also for infinite families. Declarations ending in `Statement`
define propositions to be checked.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmundVerification.Challenges

noncomputable section

/-- The union of the ordinary-coordinate rectangles. -/
def shadow {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i : Fin m, Box (Fin (d i)))) : Set (Fin (∑ i, d i) → ℝ) :=
  ⋃ R : G, rectangle R.1

/-- The extended-valued overlap; a divergent countable sum has value infinity. -/
def overlap {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i : Fin m, Box (Fin (d i))))
    (x : Fin (∑ i, d i) → ℝ) : ℝ≥0∞ :=
  ∑' R : G, (rectangle R.1).indicator (fun _ => (1 : ℝ≥0∞)) x

/-- Sparsity means measurable, pairwise-disjoint subsets of the rectangles
with the stated fraction of their Lebesgue measure. Values off `G` are irrelevant. -/
def sparse {m : ℕ} {d : Fin m → ℕ} (η : ℝ)
    (G : Set (∀ i : Fin m, Box (Fin (d i)))) : Prop :=
  ∃ E : (∀ i : Fin m, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ),
    (∀ R ∈ G, MeasurableSet (E R)) ∧
    (∀ R ∈ G, E R ⊆ rectangle R) ∧
    G.Pairwise (fun R S => Disjoint (E R) (E S)) ∧
    ∀ R ∈ G, ENNReal.ofReal η * volume (rectangle R) ≤ volume (E R)

/-- Desired `thm:overlap`: dimension-only constants, all real moments `q ≥ 2`,
and the exponential estimate on the finite shadow. Almost-everywhere finiteness
is an explicit conclusion before either use of the real representative. -/
def incomparableOverlapStatement : Prop :=
  ∃ C c : ℕ → ℕ → ℝ,
    (∀ m D, 0 < C m D) ∧ (∀ m D, 0 < c m D) ∧
    ∀ (m : ℕ) (d : Fin m → ℕ), 2 ≤ m → (∀ i : Fin m, 0 < d i) →
      ∀ (D : ∀ i : Fin m, ReyZygmund.Geometry.DyadicGrid (d i))
        (G : Set (∀ i : Fin m, Box (Fin (d i)))),
        G ⊆ gridRectangles D →
        (∀ R ∈ G, ∀ S ∈ G, rectangle R ⊆ rectangle S → R = S) →
        ∀ (η : ℝ), 0 < η → η ≤ 1 → sparse η G → volume (shadow G) < ∞ →
          (∀ᵐ x ∂volume, overlap G x < ∞) ∧
          (∀ (q : ℝ), 2 ≤ q →
            eLpNorm (fun x => (overlap G x).toReal) (ENNReal.ofReal q) volume ≤
              ENNReal.ofReal (C m (∑ i, d i) * η⁻¹ * q ^ (m - 1)) *
                (volume (shadow G)) ^ (1 / q)) ∧
          (∫⁻ x in shadow G, ENNReal.ofReal
            (Real.exp (c m (∑ i, d i) *
              Real.rpow (η * (overlap G x).toReal) (1 / ((m - 1 : ℕ) : ℝ))) - 1)
              ∂volume) ≤ ENNReal.ofReal (C m (∑ i, d i)) * volume (shadow G)

/-- The weaker-containment statement: the maximal estimate has the paper's exponent
range and requires neither sparseness nor finite shadow. The two overlap
conclusions have these additional hypotheses. -/
def weakerContainmentStatement : Prop :=
  ∃ C c : ℕ → ℕ → ℝ,
    (∀ m D, 0 < C m D) ∧ (∀ m D, 0 < c m D) ∧
    ∀ (m : ℕ) (d : Fin m → ℕ), 2 ≤ m → (∀ i : Fin m, 0 < d i) →
      ∀ (D : ∀ i : Fin m, ReyZygmund.Geometry.DyadicGrid (d i))
        (G : Set (∀ i : Fin m, Box (Fin (d i)))),
        G ⊆ gridRectangles D →
        (∀ R ∈ G, ∀ S ∈ G, rectangle R ⊆ rectangle S →
          ∃ i : Fin m, R i = S i) →
        ((∀ (p : ℝ), 1 < p → p ≤ 2 →
          ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ),
            MemLp f (ENNReal.ofReal p) volume →
            (∀ᵐ x ∂volume, absoluteMaximal G f x < ∞) ∧
              eLpNorm (fun x => (absoluteMaximal G f x).toReal)
                  (ENNReal.ofReal p) volume ≤
                ENNReal.ofReal (C m (∑ i, d i) * (p / (p - 1)) ^ (m - 1)) *
                  eLpNorm f (ENNReal.ofReal p) volume) ∧
        (∀ (η : ℝ), 0 < η → η ≤ 1 → sparse η G → volume (shadow G) < ∞ →
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

end ReyZygmundVerification.Challenges
