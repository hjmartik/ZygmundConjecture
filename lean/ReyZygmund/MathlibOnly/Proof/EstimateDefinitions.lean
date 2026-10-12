import ReyZygmund.MathlibOnly.Proof.Definitions
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Weak incomparability, sparseness and rounded rectangles

The definitions spell out weak incomparability:
strict containment cannot hold in every coordinate at once. It applies to
families of boxes; dyadic-grid membership is a separate hypothesis.
Sparse subsets are Lebesgue measurable. The rounded operator uses the paper's
`[lower, upper)` shifted rectangles. These definitions are used in the supporting estimates.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.MathlibOnly.Proof.Estimates

/-- Weak incomparability: no two rectangles
are strictly nested in every factor. -/
def WeaklyIncomparable {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i)))) : Prop :=
  ∀ R ∈ G, ∀ S ∈ G, ¬ ∀ i, R i < S i

/-- Pairwise disjoint Lebesgue-measurable subsets of the rectangles, with the
specified volume fraction. -/
def Sparse {m : ℕ} {d : Fin m → ℕ} (eta : ℝ)
    (G : Set (∀ i, Box (Fin (d i)))) : Prop :=
  ∃ E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ),
    (∀ R ∈ G, NullMeasurableSet (E R) volume ∧ E R ⊆ rectangle R ∧
      ENNReal.ofReal eta * volume (rectangle R) ≤ volume (E R)) ∧
    G.Pairwise (fun R S => Disjoint (E R) (E S))

/-- The `[lower, upper)` rectangle used by the prescribed shifted grids. -/
def rectangleIco {m : ℕ} {d : Fin m → ℕ} (R : ∀ i, Box (Fin (d i))) :
    Set (Fin (∑ i, d i) → ℝ) :=
  {x | ∀ i j, (R i).lower j ≤ x (finSigmaFinEquiv (n := d) ⟨i, j⟩) ∧
    x (finSigmaFinEquiv (n := d) ⟨i, j⟩) < (R i).upper j}

/-- Supremum of absolute Lebesgue averages over the `[lower, upper)` rectangles
containing the point. -/
noncomputable def maximalIco {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (x : Fin (∑ i, d i) → ℝ) : ℝ≥0∞ :=
  ⨆ R : G, (rectangleIco R.1).indicator
    (fun _ => (∫⁻ y in rectangleIco R.1, ENNReal.ofReal |f y| ∂volume) /
      volume (rectangleIco R.1)) x

end ReyZygmund.MathlibOnly.Proof.Estimates
