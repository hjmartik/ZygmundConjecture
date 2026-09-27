import ReyZygmund.Projection.TopAverageExpansion

/-! Explicit expected partial telescope and top-average decomposition. -/

open BoxIntegral
open scoped BigOperators
open ReyZygmund.Geometry ReyZygmund.Projection

namespace ReyZygmundVerification

def partialTelescopeTopAveragesContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ), (∀ i, 0 < d i) →
  ∀ (F : boundedMeasurableFunctions d), ProductLeafConstant I N F.1 →
    (∀ x, x ∉ productBox I → F.1 x = 0) →
  ∀ (A : Finset (Fin m)) (x : ProductPoint d), x ∈ productBox I →
    (∑ L ∈ partialInterior I N A, (productDifferenceMap A L F).1 x) =
      ∑ B ∈ A.powerset, (-1 : ℝ) ^ B.card * (productAverageMap B I F).1 x

def projectionTopAverageDecompositionContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ), (∀ i, 0 < d i) →
  ∀ (G : Finset (∀ i, Box (Fin (d i)))) (f : boundedMeasurableFunctions d),
    ProductLeafConstant I N f.1 → (∀ x, x ∉ productBox I → f.1 x = 0) →
  ∀ (A : Finset (Fin m)) (x : ProductPoint d), x ∈ productBox I →
    (∑ L ∈ partialInterior I N A,
      (productDifferenceMap A L (finiteProjectionMap I N G f)).1 x) =
      (finiteProjectionMap I N G f).1 x +
        ∑ B ∈ A.powerset.erase ∅,
          (-1 : ℝ) ^ B.card * (productAverageMap B I f).1 x

end ReyZygmundVerification
