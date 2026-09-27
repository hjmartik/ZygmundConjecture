import Mathlib.Analysis.BoxIntegral.Box.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

/-! # Mathematical definitions for the independent statements

This file depends only on Mathlib. Rectangles are subsets of Euclidean space;
averages of absolute values, suprema and overlaps take nonnegative extended
values.

We use Mathlib's half-open convention `(lower, upper]`. The grid index `k` is a
side-length exponent: side `2 ^ k`, children at `k - 1`. The grid definition
specifies geometry; countability is proved later, and a common ancestor is not
assumed.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.MathlibOnly

/-- A dyadic cube grid, indexed by the logarithm of the side length.
Each scale partitions the whole space, and intersecting cubes are nested.
These are the geometric conditions in the paper, without a choice of parent,
children or a common ancestor. -/
structure CubeGrid (d : ℕ) where
  cubes : ℤ → Set (Box (Fin d))
  side_length : ∀ k Q, Q ∈ cubes k → ∀ j,
    Q.upper j - Q.lower j = (2 : ℝ) ^ k
  pairwise_disjoint : ∀ k, (cubes k).Pairwise
    (fun Q R => Disjoint (Q : Set (Fin d → ℝ)) (R : Set (Fin d → ℝ)))
  covers : ∀ k x, ∃ Q ∈ cubes k, x ∈ Q
  nested : ∀ k l Q R, Q ∈ cubes k → R ∈ cubes l →
    (Disjoint (Q : Set (Fin d → ℝ)) (R : Set (Fin d → ℝ))) ∨ Q ≤ R ∨ R ≤ Q

noncomputable section

/-- The product rectangle in ordinary coordinates, with the block coordinates
listed by Mathlib's finite-sum equivalence. -/
def rectangle {m : ℕ} {d : Fin m → ℕ} (R : ∀ i, Box (Fin (d i))) :
    Set (Fin (∑ i, d i) → ℝ) :=
  {x | ∀ i j, (R i).lower j < x (finSigmaFinEquiv (n := d) ⟨i, j⟩) ∧
    x (finSigmaFinEquiv (n := d) ⟨i, j⟩) ≤ (R i).upper j}

/-- All products of cubes in the supplied grids, at independently chosen scales. -/
def gridRectangles {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, CubeGrid (d i)) :
    Set (∀ i, Box (Fin (d i))) :=
  {R | ∀ i, ∃ k : ℤ, R i ∈ (D i).cubes k}

/-- The union of the rectangles, not a sum counting multiplicity. -/
def shadow {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i)))) :
    Set (Fin (∑ i, d i) → ℝ) :=
  ⋃ R : G, rectangle R.1

/-- The overlap counts multiplicity and may initially be infinite. -/
def overlap {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i))))
    (x : Fin (∑ i, d i) → ℝ) : ℝ≥0∞ :=
  ∑' R : G, (rectangle R.1).indicator (fun _ => (1 : ℝ≥0∞)) x

/-- Pairwise disjoint measurable subsets establishing sparseness. -/
def Sparse {m : ℕ} {d : Fin m → ℕ} (eta : ℝ)
    (G : Set (∀ i, Box (Fin (d i)))) : Prop :=
  ∃ E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ),
    (∀ R ∈ G, MeasurableSet (E R) ∧ E R ⊆ rectangle R ∧
      ENNReal.ofReal eta * volume (rectangle R) ≤ volume (E R)) ∧
    G.Pairwise (fun R S => Disjoint (E R) (E S))

/-- No distinct members contain one another. -/
def Incomparable {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i)))) : Prop :=
  ∀ R ∈ G, ∀ S ∈ G, rectangle R ⊆ rectangle S → R = S

/-- Containment leaves at least one entire cube factor unchanged. -/
def HasEqualFactorOnContainment {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i)))) : Prop :=
  ∀ R ∈ G, ∀ S ∈ G, rectangle R ⊆ rectangle S → ∃ i, R i = S i

/-- The supremum of the averages of `|f|` over rectangles containing the point. The
averages use nonnegative integrals and may be infinite. -/
def maximal {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (x : Fin (∑ i, d i) → ℝ) : ℝ≥0∞ :=
  ⨆ R : G, (rectangle R.1).indicator
    (fun _ => (∫⁻ y in rectangle R.1, ENNReal.ofReal |f y| ∂volume) /
      volume (rectangle R.1)) x

/-- All positions and all positive first side lengths of the continuous family. -/
def continuousRectangles {n : ℕ} (d : Fin (n + 1) → ℕ)
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) :
    Set (∀ i, Box (Fin (d i))) :=
  {R | ∃ s : Fin n → Set.Ioi (0 : ℝ), ∀ i j,
    (R i).upper j - (R i).lower j =
      (Fin.snoc (fun a => (s a).1) (phi s).1 : Fin (n + 1) → ℝ) i}

/-- Prescribed-scale rounding, including the exact additive constant two. -/
def rounding (s : ℝ) : ℤ := ⌈Real.logb 2 s⌉ + 2

/-- The full image of rounding; not a single-valued graph on integer scales. -/
def roundedScales {n : ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) :
    Set (Fin (n + 1) → ℤ) :=
  Set.range (fun s : Fin n → Set.Ioi (0 : ℝ) =>
    Fin.snoc (fun i => rounding (s i).1) (rounding (phi s).1))

/-- A shifted cube is specified directly by its lower and upper corners.
The shift entries are the numerators of `0, 1/3, 2/3`. -/
def shiftedCubes {d : ℕ} (tau : Fin d → Fin 3) (k : ℤ) :
    Set (Box (Fin d)) :=
  {Q | ∃ z : Fin d → ℤ, ∀ j,
    Q.lower j = (2 : ℝ) ^ k *
      ((z j : ℝ) + (-1 : ℝ) ^ k * ((tau j).val : ℝ) / 3) ∧
    Q.upper j = Q.lower j + (2 : ℝ) ^ k}

/-- Every rectangle in the indicated shifted grids whose scale tuple is in
the full rounded image. No grid from the proof library is used here. -/
def roundedRectangles {n : ℕ} {d : Fin (n + 1) → ℕ}
    (tau : ∀ i, Fin (d i) → Fin 3)
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) :
    Set (∀ i, Box (Fin (d i))) :=
  {R | ∃ k ∈ roundedScales phi, ∀ i, R i ∈ shiftedCubes (tau i) (k i)}

/-- Dyadic Φ-Zygmund rectangles, indexed by side-length exponents.
The last exponent is determined by `Phi`. -/
def phiRectangles {n : ℕ} {d : Fin (n + 1) → ℕ}
    (D : ∀ i, CubeGrid (d i)) (Phi : (Fin n → ℤ) → ℤ) :
    Set (∀ i, Box (Fin (d i))) :=
  {R | ∃ k : Fin n → ℤ,
    ∀ i, R i ∈ (D i).cubes ((Fin.snoc k (Phi k) : Fin (n + 1) → ℤ) i)}

end
end ReyZygmund.MathlibOnly
