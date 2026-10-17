import ReyZygmund.Geometry.Grids
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

/-! # The incomparable maximal estimate and almost-everywhere finiteness

The shared definitions supply the rectangles, grids and supremum of averages
of `|f|`. The statement includes almost-everywhere finiteness before taking
the norm of the real-valued representative.

The space `Fin (∑ i, d i) → ℝ` carries Lebesgue measure. Cubes use `(lower,
upper]`. Nonnegative integration permits infinite averages.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

open ReyZygmund.MathlibOnly (gridRectangles rectangle maximal)

namespace ReyZygmundVerification

noncomputable section

/-- The incomparable maximal estimate for every `p > 1`. Its dimensional
constant is chosen before the block dimensions, grids, family, exponent and input. -/
def incomparableMaximalStatement : Prop :=
  ∃ C : ℕ → ℕ → ℝ, (∀ m D, 0 < C m D) ∧
    ∀ (m : ℕ) (d : Fin m → ℕ), 2 ≤ m → (∀ i : Fin m, 0 < d i) →
      ∀ (D : ∀ i : Fin m, ReyZygmund.MathlibOnly.CubeGrid (d i))
        (G : Set (∀ i : Fin m, Box (Fin (d i)))),
        G ⊆ gridRectangles D →
        (∀ R ∈ G, ∀ S ∈ G, rectangle R ⊆ rectangle S → R = S) →
        ∀ (p : ℝ), 1 < p →
          ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ),
            MemLp f (ENNReal.ofReal p) volume →
            (∀ᵐ x ∂volume, maximal G f x < ∞) ∧
              eLpNorm (fun x => (maximal G f x).toReal)
                  (ENNReal.ofReal p) volume ≤
                ENNReal.ofReal (C m (∑ i, d i) * (p / (p - 1)) ^ (m - 1)) *
                  eLpNorm f (ENNReal.ofReal p) volume

end

end ReyZygmundVerification
