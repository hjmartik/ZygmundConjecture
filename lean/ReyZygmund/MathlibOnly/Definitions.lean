import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.BoxIntegral.Box.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Rectangles, families and maximal functions

These definitions use Mathlib and are independent of the proof library.
`Fin m` indexes the `m` coordinate factors, of dimensions `d i`.
The grid index `k` is the side-length exponent: cubes have side `2 ^ k`.
Lean's `⊆` denotes inclusion and `⊂` strict inclusion of sets.

The sets `rectangle R` use `(lower, upper]` in each scalar coordinate.
For the explicit shifted grids, `cubeIco` and `rectangleIco` use `[lower, upper)`.
The [definition guide](DEFINITIONS.md#boundary-conventions) explains the boundary identifications.
All measures and integrals are with respect to Lebesgue measure.

The type `ℝ≥0∞` denotes `[0, ∞]`, and `∫⁻` is the nonnegative Lebesgue integral.
`∑'` denotes a possibly infinite sum, and `⨆` an indexed supremum.
For nonnegative `t`, `ENNReal.ofReal t` is the same value in `[0, ∞]`.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.MathlibOnly

/-- Euclidean space of dimension `∑ i, d i`. -/
abbrev Point {m : ℕ} (d : Fin m → ℕ) := Fin (∑ i, d i) → ℝ

/-- A tuple of nonempty box factors. The grid and side-length conditions
below select products of cubes. -/
abbrev Rectangle {m : ℕ} (d : Fin m → ℕ) := ∀ i, Box (Fin (d i))

/-- A dyadic cube grid: cubes of side `2 ^ k` partition the space at each
integer scale, and intersecting cubes are nested. -/
structure CubeGrid (d : ℕ) where
  cubes : ℤ → Set (Box (Fin d))
  side_length : ∀ k Q, Q ∈ cubes k → ∀ j,
    Q.upper j - Q.lower j = (2 : ℝ) ^ k
  pairwise_disjoint : ∀ k, (cubes k).Pairwise
    (fun Q R => Disjoint (Q : Set (Fin d → ℝ)) (R : Set (Fin d → ℝ)))
  covers : ∀ k x, ∃ Q ∈ cubes k, x ∈ Q
  nested : ∀ k l Q R, Q ∈ cubes k → R ∈ cubes l →
    Disjoint (Q : Set (Fin d → ℝ)) (R : Set (Fin d → ℝ)) ∨
      (Q : Set (Fin d → ℝ)) ⊆ (R : Set (Fin d → ℝ)) ∨
      (R : Set (Fin d → ℝ)) ⊆ (Q : Set (Fin d → ℝ))

noncomputable section

/-- The product of the factors, with scalar coordinates listed block by block.
`finSigmaFinEquiv` assigns the scalar index to the pair `(i, j)`. -/
def rectangle {m : ℕ} {d : Fin m → ℕ} (R : Rectangle d) :
    Set (Point d) :=
  {x | ∀ i j, (R i).lower j < x (finSigmaFinEquiv (n := d) ⟨i, j⟩) ∧
    x (finSigmaFinEquiv (n := d) ⟨i, j⟩) ≤ (R i).upper j}

/-- Append the last coordinate block to a point in the first blocks.
`Fin.addCases` concatenates the two coordinate lists; `Fin.cast` uses the
identity that the total dimension is the sum of their dimensions. -/
def appendLastPoint {n : ℕ} {d : Fin (n + 1) → ℕ}
    (x : Point (fun i : Fin n => d i.castSucc))
    (t : Fin (d (Fin.last n)) → ℝ) : Point d :=
  fun j => Fin.addCases x t (Fin.cast (Fin.sum_univ_castSucc d) j)

/-- Projection of a rectangle onto its first `n` factors.
`i.castSucc` regards an index of these factors as an index of all `n + 1`. -/
def initialProjection {n : ℕ} {d : Fin (n + 1) → ℕ} (R : Rectangle d) :
    Rectangle (fun i : Fin n => d i.castSucc) := fun i => R i.castSucc

/-- All products of cubes in the supplied grids, at independently chosen scales. -/
def gridRectangles {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, CubeGrid (d i)) :
    Set (Rectangle d) :=
  {R | ∀ i, ∃ k : ℤ, R i ∈ (D i).cubes k}

/-- The shadow: the union of the rectangles in the family.
In expressions indexed by `R : G`, `R` ranges over the rectangles belonging to `G`,
and `R.1` denotes the rectangle itself. -/
def shadow {m : ℕ} {d : Fin m → ℕ} (G : Set (Rectangle d)) :
    Set (Point d) :=
  ⋃ R : G, rectangle R.1

/-- The overlap: the sum of rectangle indicators, counting the members of `G`
containing `x`, with values in `[0, ∞]`. -/
def overlap {m : ℕ} {d : Fin m → ℕ} (G : Set (Rectangle d))
    (x : Point d) : ℝ≥0∞ :=
  ∑' R : G, (rectangle R.1).indicator (fun _ => (1 : ℝ≥0∞)) x

/-- The slice above `t` in the last coordinate block: the projections of those
rectangles whose last factor contains `t`. `Fin.last n` is the last index,
and `''` denotes the image of a set. Repeated projections occur only once. -/
def sliceFamily {n : ℕ} {d : Fin (n + 1) → ℕ}
    (G : Set (Rectangle d)) (t : Fin (d (Fin.last n)) → ℝ) :
    Set (Rectangle (fun i : Fin n => d i.castSucc)) :=
  initialProjection '' {R | R ∈ G ∧ t ∈ R (Fin.last n)}

/-- No distinct members contain one another. -/
def Incomparable {m : ℕ} {d : Fin m → ℕ}
    (G : Set (Rectangle d)) : Prop :=
  ∀ R ∈ G, ∀ S ∈ G, rectangle R ⊆ rectangle S → R = S

/-- Weak incomparability: strict containment cannot hold in every factor.
Here `⊂` denotes strict inclusion of sets. -/
def WeaklyIncomparable {m : ℕ} {d : Fin m → ℕ}
    (G : Set (Rectangle d)) : Prop :=
  ∀ R ∈ G, ∀ S ∈ G, ¬ ∀ i,
    (R i : Set (Fin (d i) → ℝ)) ⊂ (S i : Set (Fin (d i) → ℝ))

/-- Sparseness: pairwise disjoint Lebesgue-measurable sets `E R ⊆ rectangle R`
with measure at least `eta` times the rectangle's measure.
`NullMeasurableSet` expresses measurability for completed Lebesgue measure. -/
def Sparse {m : ℕ} {d : Fin m → ℕ} (eta : ℝ)
    (G : Set (Rectangle d)) : Prop :=
  ∃ E : Rectangle d → Set (Point d),
    (∀ R ∈ G, NullMeasurableSet (E R) volume ∧ E R ⊆ rectangle R ∧
      ENNReal.ofReal eta * volume (rectangle R) ≤ volume (E R)) ∧
    G.Pairwise (fun R S => Disjoint (E R) (E S))

/-- The supremum of the averages of `|f|` over rectangles containing `x`.
`⨆ (_ : x ∈ rectangle R)` restricts the supremum to rectangles containing `x`.
The supremum is zero when no rectangle contains `x`. -/
def maximal {m : ℕ} {d : Fin m → ℕ} (G : Set (Rectangle d))
    (f : Point d → ℝ) (x : Point d) : ℝ≥0∞ :=
  ⨆ R ∈ G, ⨆ (_ : x ∈ rectangle R),
    (∫⁻ y in rectangle R, ENNReal.ofReal |f y| ∂volume) /
      volume (rectangle R)

/-- The Zygmund rectangles with side lengths `(s₁, …, sₙ, phi s)`, at every position
and for every positive tuple `s`. The type `Set.Ioi (0 : ℝ)` means `(0, ∞)`;
`Fin.snoc` appends the prescribed last side length. -/
def zygmundRectangles {n : ℕ} (d : Fin (n + 1) → ℕ)
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) :
    Set (Rectangle d) :=
  {R | ∃ s : Fin n → Set.Ioi (0 : ℝ), ∀ i j,
    (R i).upper j - (R i).lower j =
      (Fin.snoc (fun a => (s a).1) (phi s).1 : Fin (n + 1) → ℝ) i}

/-- The rounding rule `ρ(s) = ⌈log₂ s⌉ + 2` for positive side lengths. -/
def rounding (s : ℝ) : ℤ := ⌈Real.logb 2 s⌉ + 2

/-- All rounded tuples `(ρ(s₁), …, ρ(sₙ), ρ(phi s))`.
A fixed tuple of the first `n` rounded scales can have several last scales. -/
def roundedScales {n : ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) :
    Set (Fin (n + 1) → ℤ) :=
  Set.range (fun s : Fin n → Set.Ioi (0 : ℝ) =>
    Fin.snoc (fun i => rounding (s i).1) (rounding (phi s).1))

/-- Corners of the cubes `2^k ([0,1)^d + z + (-1)^k tau/3)`.
Each entry of `tau : Fin d → Fin 3` is `0`, `1` or `2`.
The associated `[lower, upper)` sets are used by the `Ico` definitions below. -/
def shiftedCubes {d : ℕ} (tau : Fin d → Fin 3) (k : ℤ) :
    Set (Box (Fin d)) :=
  {Q | ∃ z : Fin d → ℤ, ∀ j,
    Q.lower j = (2 : ℝ) ^ k *
      ((z j : ℝ) + (-1 : ℝ) ^ k * ((tau j).val : ℝ) / 3) ∧
    Q.upper j = Q.lower j + (2 : ℝ) ^ k}

/-- Products of shifted cubes whose side-length exponents belong to
`roundedScales phi`. -/
def roundedRectangles {n : ℕ} {d : Fin (n + 1) → ℕ}
    (tau : ∀ i, Fin (d i) → Fin 3)
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) :
    Set (Rectangle d) :=
  {R | ∃ k ∈ roundedScales phi, ∀ i, R i ∈ shiftedCubes (tau i) (k i)}

/-- The `[lower, upper)` rectangle used by the prescribed shifted grids. -/
def rectangleIco {m : ℕ} {d : Fin m → ℕ} (R : Rectangle d) :
    Set (Point d) :=
  {x | ∀ i j, (R i).lower j ≤ x (finSigmaFinEquiv (n := d) ⟨i, j⟩) ∧
    x (finSigmaFinEquiv (n := d) ⟨i, j⟩) < (R i).upper j}

/-- The `[lower, upper)` cube with the given corners. -/
def cubeIco {d : ℕ} (Q : Box (Fin d)) : Set (Fin d → ℝ) :=
  {x | ∀ j, Q.lower j ≤ x j ∧ x j < Q.upper j}

/-- Partition and nesting of the cubes of `D` with `[lower, upper)` boundaries. -/
def IcoGrid {d : ℕ} (D : CubeGrid d) : Prop :=
  (∀ k, (D.cubes k).Pairwise (fun Q R => Disjoint (cubeIco Q) (cubeIco R))) ∧
  (∀ k x, ∃ Q ∈ D.cubes k, x ∈ cubeIco Q) ∧
  ∀ k l Q R, Q ∈ D.cubes k → R ∈ D.cubes l →
    Disjoint (cubeIco Q) (cubeIco R) ∨ cubeIco Q ⊆ cubeIco R ∨ cubeIco R ⊆ cubeIco Q

/-- Overlap counting for rectangles with `[lower, upper)` boundaries. -/
def overlapIco {m : ℕ} {d : Fin m → ℕ} (G : Set (Rectangle d))
    (x : Point d) : ℝ≥0∞ :=
  ∑' R : G, (rectangleIco R.1).indicator (fun _ => (1 : ℝ≥0∞)) x

/-- A slice using `[lower, upper)` membership in the last factor. -/
def sliceFamilyIco {n : ℕ} {d : Fin (n + 1) → ℕ}
    (G : Set (Rectangle d)) (t : Fin (d (Fin.last n)) → ℝ) :
    Set (Rectangle (fun i : Fin n => d i.castSucc)) :=
  initialProjection '' {R | R ∈ G ∧ t ∈ cubeIco (R (Fin.last n))}

/-- The supremum of the averages of `|f|` over the `[lower, upper)` rectangles
containing `x`. -/
def maximalIco {m : ℕ} {d : Fin m → ℕ}
    (G : Set (Rectangle d))
    (f : Point d → ℝ) (x : Point d) : ℝ≥0∞ :=
  ⨆ R ∈ G, ⨆ (_ : x ∈ rectangleIco R),
    (∫⁻ y in rectangleIco R, ENNReal.ofReal |f y| ∂volume) /
      volume (rectangleIco R)

/-- The dyadic Φ-Zygmund rectangles: products of grid cubes with side lengths
`(2^k₁, …, 2^kₙ, 2^(Phi k))`. -/
def dyadicZygmundRectangles {n : ℕ} {d : Fin (n + 1) → ℕ}
    (D : ∀ i, CubeGrid (d i)) (Phi : (Fin n → ℤ) → ℤ) :
    Set (Rectangle d) :=
  {R | ∃ k : Fin n → ℤ,
    ∀ i, R i ∈ (D i).cubes ((Fin.snoc k (Phi k) : Fin (n + 1) → ℤ) i)}

/-- The exponential on `[0, ∞]`: the usual `e^t` for finite `t`, and `∞` at `∞`. -/
def exp (t : ℝ≥0∞) : ℝ≥0∞ := EReal.exp (t : EReal)

end
end ReyZygmund.MathlibOnly
