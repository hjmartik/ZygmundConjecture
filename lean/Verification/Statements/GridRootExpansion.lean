import ReyZygmund.Geometry.FiniteSquare
import ReyZygmund.Projection.FiniteIndices

/-! Statements for a finite difference sum inside a top rectangle. -/

open BoxIntegral
open scoped BigOperators Classical

namespace ReyZygmundVerification

open ReyZygmund.Geometry ReyZygmund.Projection

def finiteDifferenceSumProductStepContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (H : Finset (∀ i, Box (Fin (d i)))), H ⊆ productInterior I N →
      ∀ (F : boundedMeasurableFunctions d),
        let S := ∑ Q ∈ H, productDifferenceMap Finset.univ Q F
        ProductLeafConstant I N S.1 ∧ ∀ x, x ∉ productBox I → S.1 x = 0

def finiteDifferenceSumReexpansionContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ i, 0 < d i) → ∀ (H : Finset (∀ i, Box (Fin (d i)))),
      H ⊆ productInterior I N → ∀ (F : boundedMeasurableFunctions d),
        let S := ∑ Q ∈ H, productDifferenceMap Finset.univ Q F
        S = ∑ L ∈ productInterior I N, productDifferenceMap Finset.univ L S

def finiteDifferenceSumSquareContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ i, 0 < d i) → ∀ (H : Finset (∀ i, Box (Fin (d i)))),
      H ⊆ productInterior I N → ∀ (F : boundedMeasurableFunctions d) (x : ProductPoint d),
        let S := ∑ Q ∈ H, productDifferenceMap Finset.univ Q F
        finiteSquareFunction I N Finset.univ S x =
          Real.sqrt (∑ Q ∈ H, ((productDifferenceMap Finset.univ Q F).1 x) ^ 2)

end ReyZygmundVerification
