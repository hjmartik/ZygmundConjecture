import ReyZygmund.Geometry.Grids
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

/-! # An independent maximal statement in Euclidean coordinates

The geometric dyadic-grid structure is imported, while rectangles, averages of
`|f|` and their supremum are defined here without the maximal proofs or operator
definitions. The final declaration defines the proposition to be checked.

The space `Fin (∑ i, d i) → ℝ` carries Lebesgue measure. Cubes use `(lower,
upper]`. Nonnegative integration permits infinite averages.




-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmundVerification.Challenges

noncomputable section

/-- The rectangle in consecutive ordinary Euclidean coordinates. -/
def rectangle {m : ℕ} {d : Fin m → ℕ}
    (R : ∀ i : Fin m, Box (Fin (d i))) : Set (Fin (∑ i, d i) → ℝ) :=
  {x | ∀ (i : Fin m) (k : Fin (d i)),
    (R i).lower k < x (finSigmaFinEquiv (n := d) ⟨i, k⟩) ∧
      x (finSigmaFinEquiv (n := d) ⟨i, k⟩) ≤ (R i).upper k}

/-- All tuples selected from the supplied grids, at arbitrary integer scales. -/
def gridRectangles {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i : Fin m, ReyZygmund.Geometry.DyadicGrid (d i)) :
    Set (∀ i : Fin m, Box (Fin (d i))) :=
  {R | ∀ i : Fin m, ∃ n : ℤ, R i ∈ (D i).cubes n}

/-- The positive maximal function, with a nonnegative integral in each
rectangle and a supported extended-valued supremum. -/
def absoluteMaximal {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i : Fin m, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ)
    (x : Fin (∑ i, d i) → ℝ) : ℝ≥0∞ :=
  ⨆ R : G, (rectangle R.1).indicator
    (fun _ => (∫⁻ y in rectangle R.1, ENNReal.ofReal |f y| ∂volume) /
      volume (rectangle R.1)) x

/-- Desired main statement, including almost-everywhere finiteness before the
norm of the real representative. Its dimensional constant is chosen before
the block dimensions, grids, family, exponent and input. No proof is asserted. -/
def incomparableMaximalStatement : Prop :=
  ∃ C : ℕ → ℕ → ℝ, (∀ m D, 0 < C m D) ∧
    ∀ (m : ℕ) (d : Fin m → ℕ), 2 ≤ m → (∀ i : Fin m, 0 < d i) →
      ∀ (D : ∀ i : Fin m, ReyZygmund.Geometry.DyadicGrid (d i))
        (G : Set (∀ i : Fin m, Box (Fin (d i)))),
        G ⊆ gridRectangles D →
        (∀ R ∈ G, ∀ S ∈ G, rectangle R ⊆ rectangle S → R = S) →
        ∀ (p : ℝ), 1 < p →
          ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ),
            MemLp f (ENNReal.ofReal p) volume →
            (∀ᵐ x ∂volume, absoluteMaximal G f x < ∞) ∧
              eLpNorm (fun x => (absoluteMaximal G f x).toReal)
                  (ENNReal.ofReal p) volume ≤
                ENNReal.ofReal (C m (∑ i, d i) * (p / (p - 1)) ^ (m - 1)) *
                  eLpNorm f (ENNReal.ofReal p) volume

end

end ReyZygmundVerification.Challenges
