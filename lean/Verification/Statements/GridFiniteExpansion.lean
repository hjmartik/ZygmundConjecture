import ReyZygmund.Geometry.GridFiniteExpansion

/-! Explicit contracts for finite expansions in the full grid. -/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmundVerification

open ReyZygmund.Geometry

def gridRawDifferenceSumContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (D : ∀ i, DyadicGrid (d i)),
    (∀ i, 0 < d i) → ∀ (H : Finset (∀ i, Box (Fin (d i)))),
      (↑H : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D →
      ∀ (F : boundedMeasurableFunctions d) (L : ∀ i, Box (Fin (d i))),
        L ∈ gridRectangles D →
        rawProductDifference L (fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x) =
          if L ∈ H then rawProductDifference L F.1 else 0

def gridRawDifferenceOutsideExpansionContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (D : ∀ i, DyadicGrid (d i)),
    (∀ i, 0 < d i) → ∀ (H : Finset (∀ i, Box (Fin (d i)))),
      (↑H : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D →
      ∀ (F : boundedMeasurableFunctions d),
        (F.1 = fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x) →
        ∀ (L : ∀ i, Box (Fin (d i))), L ∈ gridRectangles D → L ∉ H →
          rawProductDifference L F.1 = 0

def fullGridSquareFiniteExpansionContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (D : ∀ i, DyadicGrid (d i)),
    (∀ i, 0 < d i) → ∀ (H : Finset (∀ i, Box (Fin (d i)))),
      (↑H : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D →
      ∀ (F : boundedMeasurableFunctions d),
        (F.1 = fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x) →
        ∀ (x : ProductPoint d), fullGridSquare D F.1 x =
          (∑ Q ∈ H, (ENNReal.ofReal |rawProductDifference Q F.1 x|) ^ 2) ^ (1 / 2 : ℝ)

def gridAverageFiniteExpansionZeroContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (D : ∀ i, DyadicGrid (d i)),
    (∀ i, 0 < d i) → ∀ (H : Finset (∀ i, Box (Fin (d i)))),
      (↑H : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D →
      ∀ (F : boundedMeasurableFunctions d),
        (F.1 = fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x) →
        ∀ (R : ∀ i, Box (Fin (d i))), R ∈ gridRectangles D →
          (∀ Q ∈ H, ∃ i, ¬ R i < Q i) → productAverageMap Finset.univ R F = 0

def gridMeanFiniteExpansionZeroContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (D : ∀ i, DyadicGrid (d i)),
    (∀ i, 0 < d i) → ∀ (H : Finset (∀ i, Box (Fin (d i)))),
      (↑H : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D →
      ∀ (F : boundedMeasurableFunctions d),
        (F.1 = fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x) →
        ∀ (R : ∀ i, Box (Fin (d i))), R ∈ gridRectangles D →
          (∀ Q ∈ H, ∃ i, ¬ R i < Q i) →
          (∫ x in productBox R, F.1 x) / volume.real (productBox R) = 0

end ReyZygmundVerification
