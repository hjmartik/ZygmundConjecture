import ReyZygmund.Geometry.GridFamilies
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

/-! # An independently stated maximal–square estimate

The imports supply dyadic grids and children, product boxes and Lebesgue measure.
We separately define the averages, differences and square function without
importing their proof-library versions or the square estimate.

The hypothesis is a finite difference expansion almost everywhere. Essential
boundedness, integrability and the resulting finite square formula are conclusions
of the development. The square and maximum range over the whole grid, with the
absolute value outside the signed average.


-/

open BoxIntegral MeasureTheory ReyZygmund.Geometry
open scoped BigOperators ENNReal Classical

namespace ReyZygmundVerification.Challenges

noncomputable section

/-- Inclusion-exclusion of supported signed rectangle averages.
Children are selected in A and parents in its complement. -/
def squareRawDifference {m : ℕ} {d : Fin m → ℕ}
    (Q : ∀ i, Box (Fin (d i))) (g : ProductPoint d → ℝ)
    (x : ProductPoint d) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset (Fin m)).powerset,
    (-1 : ℝ) ^ (m - A.card) *
      ∑ R ∈ Fintype.piFinset (fun i =>
        if i ∈ A then (Prepartition.splitCenter (Q i)).boxes else {Q i}),
        (productBox R).indicator
          (fun _ => (∫ y in productBox R, g y ∂volume) /
            volume.real (productBox R)) x

/-- The full signed-average maximum over every grid rectangle. -/
def squareSignedMaximal {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, DyadicGrid (d i)) (g : ProductPoint d → ℝ)
    (x : ProductPoint d) : ℝ≥0∞ :=
  ⨆ Q : ReyZygmund.Geometry.gridRectangles D,
    ENNReal.ofReal ((productBox Q.1).indicator
      (fun _ => |(∫ y in productBox Q.1, g y ∂volume) /
        volume.real (productBox Q.1)|) x)

/-- The full extended square, with no finite expansion set or cutoff in its
definition. Extended summation cannot default a divergent real sum to zero. -/
def squareFunction {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, DyadicGrid (d i)) (g : ProductPoint d → ℝ)
    (x : ProductPoint d) : ℝ≥0∞ :=
  (∑' Q : ReyZygmund.Geometry.gridRectangles D,
    (ENNReal.ofReal |squareRawDifference Q.1 g x|) ^ 2) ^ (1 / 2 : ℝ)

/-- The square-function estimate includes the conclusions needed to interpret its Lp
norms. They follow from the finite-expansion hypothesis and are not added
regularity assumptions on the input. -/
def productSquareStatement : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ), 1 ≤ m → (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i))
      (H : Finset (∀ i, Box (Fin (d i)))),
      (↑H : Set (∀ i, Box (Fin (d i)))) ⊆ ReyZygmund.Geometry.gridRectangles D →
      ∀ g : ProductPoint d → ℝ,
        (g =ᵐ[volume] fun x => ∑ Q ∈ H, squareRawDifference Q g x) →
        ∀ p : ℝ, 1 ≤ p → p ≤ (3 : ℝ) / 2 →
          Integrable g volume ∧
          Measurable (squareSignedMaximal D g) ∧
          Measurable (squareFunction D g) ∧
          (∀ᵐ x ∂volume, squareSignedMaximal D g x < ∞) ∧
          (∀ᵐ x ∂volume, squareFunction D g x < ∞) ∧
          MemLp (fun x => (squareSignedMaximal D g x).toReal)
            (ENNReal.ofReal p) volume ∧
          MemLp (fun x => (squareFunction D g x).toReal)
            (ENNReal.ofReal p) volume ∧
          eLpNorm (fun x => (squareSignedMaximal D g x).toReal)
              (ENNReal.ofReal p) volume ≤
            ENNReal.ofReal ((2 : ℝ) ^ (6 * (∑ i, d i) + 10)) *
              eLpNorm (fun x => (squareFunction D g x).toReal)
                (ENNReal.ofReal p) volume

end

end ReyZygmundVerification.Challenges
