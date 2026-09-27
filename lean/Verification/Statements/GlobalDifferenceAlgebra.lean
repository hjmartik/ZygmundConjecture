import ReyZygmund.Geometry.GlobalDifferences

/-! Statements for full-grid operators, one-coordinate difference identities, and
cancellation below the smallest cubes. They were written independently of the
proofs. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmundVerification

open ReyZygmund.Geometry

def measurableSignedGridMaximalContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (D : ∀ i, DyadicGrid (d i))
    (g : ProductPoint d → ℝ), Measurable (signedGridMaximal D g)

def measurableFullGridSquareContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (D : ∀ i, DyadicGrid (d i))
    (g : ProductPoint d → ℝ), Measurable (fullGridSquare D g)

def signedGridMaximalCongrAeContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (D : ∀ i, DyadicGrid (d i))
    (g h : ProductPoint d → ℝ), g =ᵐ[volume] h →
      signedGridMaximal D g = signedGridMaximal D h

def fullGridSquareCongrAeContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (D : ∀ i, DyadicGrid (d i))
    (g h : ProductPoint d → ℝ), g =ᵐ[volume] h →
      fullGridSquare D g = fullGridSquare D h

def gridChildStrictContainmentContract : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (D : DyadicGrid d) (a b : ℤ)
    (L Q : Box (Fin d)), L ∈ D.cubes a → Q ∈ D.cubes b → L < Q →
      ∃ J, J ∈ Prepartition.splitCenter Q ∧ L ≤ J

def gridAverageDifferenceContract : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (D : DyadicGrid d) (a b : ℤ)
    (L Q : Box (Fin d)), L ∈ D.cubes a → Q ∈ D.cubes b →
      ∀ (f : (Fin d → ℝ) → ℝ),
        IntegrableOn f (Q : Set (Fin d → ℝ)) volume →
        boxAverage L (boxDifference Q f) =
          if L < Q then (L : Set (Fin d → ℝ)).indicator (boxDifference Q f) else 0

def gridDifferenceDifferenceContract : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (D : DyadicGrid d) (a b : ℤ)
    (L Q : Box (Fin d)), L ∈ D.cubes a → Q ∈ D.cubes b →
      ∀ (f : (Fin d → ℝ) → ℝ),
        IntegrableOn f (Q : Set (Fin d → ℝ)) volume →
        boxDifference L (boxDifference Q f) =
          if L = Q then boxDifference Q f else 0

def productLeafCoordinateSliceContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (I : ∀ i, Box (Fin (d i)))
    (N : Fin m → ℕ) (f : ProductPoint d → ℝ), ProductLeafConstant I N f →
      (∀ x, x ∉ productBox I → f x = 0) →
      ∀ (i : Fin m) (P : Box (Fin (d i))), P ∈ level (I i) (N i) →
        ∀ (x : ProductPoint d), ∀ y ∈ P, ∀ z ∈ P,
          f (Function.update x i y) = f (Function.update x i z)

def coordinateDifferenceBelowLeafContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (I : ∀ i, Box (Fin (d i)))
    (N : Fin m → ℕ) (f : ProductPoint d → ℝ), ProductLeafConstant I N f →
      (∀ x, x ∉ productBox I → f x = 0) →
      ∀ (i : Fin m) (P Q : Box (Fin (d i))), P ∈ level (I i) (N i) → Q ≤ P →
        coordinateDifference i Q f = 0

end ReyZygmundVerification
