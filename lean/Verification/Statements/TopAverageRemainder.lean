import ReyZygmund.Maximal.TopAverageRemainder

/-! Exact expected top-average coordinate removal and quantitative bounds. -/

open BoxIntegral MeasureTheory
open scoped BigOperators
open ReyZygmund ReyZygmund.Geometry

namespace ReyZygmundVerification

def topAverageCoordinateRemovalContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A B : Finset (Fin m)), B ⊆ A →
  ∀ (F : boundedMeasurableFunctions d), ProductLeafConstant I N F.1 →
    (∀ x, x ∉ productBox I → F.1 x = 0) →
  ∀ (x : ProductPoint d), x ∈ productBox I →
    finiteSignedPartialMaximal I N A (productAverageMap B I F) x =
      finiteSignedPartialMaximal I N (A \ B) (productAverageMap B I F) x

def topAverageIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A B : Finset (Fin m)), B ⊆ A → (∀ i ∈ A \ B, 0 < d i) →
  ∀ (F : boundedMeasurableFunctions d), ProductLeafConstant I N F.1 →
    (∀ x, x ∉ productBox I → F.1 x = 0) →
  ∀ (p : ℝ), 1 < p →
    (∫ x in productBox I,
      Real.rpow (finiteSignedPartialMaximal I N A (productAverageMap B I F) x) p) ≤
      Real.rpow (p / (p - 1)) (p * ((A \ B).card : ℝ)) *
        ∫ x in productBox I, Real.rpow |F.1 x| p

def topAverageNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m →
  ∀ (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ), (∀ i, 0 < d i) →
  ∀ (j : Fin m) (B : Finset (Fin m)), B ⊆ Finset.univ.erase j → B.Nonempty →
  ∀ (f : boundedMeasurableFunctions d), ProductLeafConstant I N f.1 →
    (∀ x, x ∉ productBox I → f.1 x = 0) →
  ∀ (p : ℝ), 1 < p →
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteSignedPartialMaximal I N (Finset.univ.erase j)
        (productAverageMap B I f) x) p) (1 / p) ≤
      (p / (p - 1)) ^ (m - 2) *
        Real.rpow (∫ x in productBox I, Real.rpow |f.1 x| p) (1 / p)

end ReyZygmundVerification
