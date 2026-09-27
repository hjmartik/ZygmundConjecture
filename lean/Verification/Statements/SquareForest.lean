import ReyZygmund.Geometry.GlobalDifferences
import ReyZygmund.Maximal.Signed
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Statements for localizing finite square functions and signed maxima to disjoint
top rectangles. Both finite operators are defined here without importing the
localization or finite-expansion proofs. -/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry ReyZygmund.Projection

def finiteDifferenceSquareMeasurableContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (H : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ),
    Measurable (fun x => Real.sqrt (∑ Q ∈ H, (rawProductDifference Q f x) ^ 2))

def finiteDifferenceSquareSupportContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (H : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ)
    (x : ProductPoint d),
    (∀ Q ∈ H, x ∉ productBox Q) →
      Real.sqrt (∑ Q ∈ H, (rawProductDifference Q f x) ^ 2) = 0

def finiteDifferenceSquareBoundedContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (H : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ),
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, Real.sqrt (∑ Q ∈ H, (rawProductDifference Q f x) ^ 2) ≤ C

def finiteDifferenceSquarePowerIntegrableContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (H : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ)
    (p : ℝ), 0 < p →
    Integrable (fun x =>
      Real.rpow (Real.sqrt (∑ Q ∈ H, (rawProductDifference Q f x) ^ 2)) p) volume

def fullSquareFiniteExpansionContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, DyadicGrid (d i)),
    (∀ i, 0 < d i) →
    ∀ (H : Finset (∀ i, Box (Fin (d i)))),
      (↑H : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D →
      ∀ (F : boundedMeasurableFunctions d),
        F.1 = (fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x) →
        ∀ x : ProductPoint d,
          fullGridSquare D F.1 x = ENNReal.ofReal
            (Real.sqrt (∑ Q ∈ H, (rawProductDifference Q F.1 x) ^ 2))

def differenceForestLocalContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (T H : Finset (∀ i, Box (Fin (d i)))),
    Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (productBox R) (productBox S)) →
    (∀ Q ∈ H, ∃ R ∈ T, ∀ i, Q i ≤ R i) →
    ∀ (F : boundedMeasurableFunctions d) (R : ∀ i, Box (Fin (d i))), R ∈ T →
      ∀ x : ProductPoint d, x ∈ productBox R →
        (∑ Q ∈ H.filter (fun Q => ∀ i, Q i ≤ R i),
          productDifferenceMap Finset.univ Q F).1 x =
            ∑ Q ∈ H, rawProductDifference Q F.1 x

def differenceSquareForestLocalContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (T H : Finset (∀ i, Box (Fin (d i)))),
    Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (productBox R) (productBox S)) →
    (∀ Q ∈ H, ∃ R ∈ T, ∀ i, Q i ≤ R i) →
    ∀ (f : ProductPoint d → ℝ) (R : ∀ i, Box (Fin (d i))), R ∈ T →
      ∀ x : ProductPoint d, x ∈ productBox R →
        Real.sqrt (∑ Q ∈ H.filter (fun Q => ∀ i, Q i ≤ R i),
          (rawProductDifference Q f x) ^ 2) =
            Real.sqrt (∑ Q ∈ H, (rawProductDifference Q f x) ^ 2)

def differenceSquareForestIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (T H : Finset (∀ i, Box (Fin (d i)))),
    Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (productBox R) (productBox S)) →
    (∀ Q ∈ H, ∃ R ∈ T, ∀ i, Q i ≤ R i) →
    ∀ (f : ProductPoint d → ℝ) (p : ℝ), 0 < p →
      (∑ R ∈ T, ∫ x in productBox R,
        Real.rpow (Real.sqrt (∑ Q ∈ H.filter (fun Q => ∀ i, Q i ≤ R i),
          (rawProductDifference Q f x) ^ 2)) p) ≤
        ∫ x, Real.rpow (Real.sqrt (∑ Q ∈ H, (rawProductDifference Q f x) ^ 2)) p

def finiteSignedMaximalForestSupportContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (T A : Finset (∀ i, Box (Fin (d i)))),
    (∀ Q ∈ A, ∃ R ∈ T, ∀ i, Q i ≤ R i) →
    ∀ (f : ProductPoint d → ℝ) (x : ProductPoint d),
      x ∉ ⋃ R ∈ T, productBox R →
      A.sup (fun Q => ENNReal.ofReal ((productBox Q).indicator
        (fun _ => |(∫ y in productBox Q, f y) / volume.real (productBox Q)|) x)) = 0

def finiteSignedMaximalForestLocalContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (T A : Finset (∀ i, Box (Fin (d i)))),
    Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (productBox R) (productBox S)) →
    (∀ Q ∈ A, ∃ R ∈ T, ∀ i, Q i ≤ R i) →
    ∀ (R : ∀ i, Box (Fin (d i))), R ∈ T → ∀ N : Fin m → ℕ,
      A.filter (fun Q => ∀ i, Q i ≤ R i) ⊆ productDescendants R N →
      ∀ (f : ProductPoint d → ℝ) (S : boundedMeasurableFunctions d),
        (∀ x ∈ productBox R, f x = S.1 x) →
        ∀ x : ProductPoint d, x ∈ productBox R →
          A.sup (fun Q => ENNReal.ofReal ((productBox Q).indicator
            (fun _ => |(∫ y in productBox Q, f y) / volume.real (productBox Q)|) x)) ≤
              ENNReal.ofReal (finiteSignedProductMaximal R N S x)

def finiteSignedMaximalForestIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (T A : Finset (∀ i, Box (Fin (d i)))),
    Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (productBox R) (productBox S)) →
    (∀ Q ∈ A, ∃ R ∈ T, ∀ i, Q i ≤ R i) →
    ∀ N : Fin m → ℕ,
      (∀ R ∈ T,
        A.filter (fun Q => ∀ i, Q i ≤ R i) ⊆ productDescendants R N) →
      ∀ (f : ProductPoint d → ℝ)
        (S : (∀ i, Box (Fin (d i))) → boundedMeasurableFunctions d),
        (∀ R ∈ T, ∀ x ∈ productBox R, f x = (S R).1 x) →
        ∀ p : ℝ, 0 < p →
          (∫⁻ x, (A.sup (fun Q => ENNReal.ofReal ((productBox Q).indicator
            (fun _ => |(∫ y in productBox Q, f y) / volume.real (productBox Q)|) x))) ^ p) ≤
            ∑ R ∈ T, ∫⁻ x in productBox R,
              (ENNReal.ofReal (finiteSignedProductMaximal R N (S R) x)) ^ p

def finiteSignedGridSquareIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, DyadicGrid (d i)),
    (∀ i, 0 < d i) →
    ∀ (H : Finset (∀ i, Box (Fin (d i)))),
      (↑H : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D →
      ∀ (F : boundedMeasurableFunctions d),
        F.1 = (fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x) →
        ∀ (A : Finset (∀ i, Box (Fin (d i)))),
          (↑A : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D →
          ∀ p : ℝ, 1 ≤ p → p ≤ (3 : ℝ) / 2 →
            (∫⁻ x, (A.sup (fun Q => ENNReal.ofReal ((productBox Q).indicator
              (fun _ => |(∫ y in productBox Q, F.1 y) / volume.real (productBox Q)|) x))) ^ p) ≤
              ENNReal.ofReal ((2 : ℝ) ^ (6 * (∑ i, d i) + 10)) *
                ENNReal.ofReal (∫ x, Real.rpow
                  (Real.sqrt (∑ Q ∈ H, (rawProductDifference Q F.1 x) ^ 2)) p)

end ReyZygmundVerification
