import ReyZygmund.Maximal.FibreSquare

/-! Exact finite partial signed maximal-square estimates. -/

open BoxIntegral MeasureTheory
open scoped BigOperators
open ReyZygmund ReyZygmund.Geometry

namespace ReyZygmundVerification

def fibreSquareIntegralContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin (n + 1) → ℕ), (∀ i, 0 < d i) →
  ∀ (F : boundedMeasurableFunctions d), ProductLeafConstant I N F.1 →
    (∀ x, x ∉ productBox I → F.1 x = 0) →
  ∀ (j : Fin (n + 1)) (p : ℝ), 1 ≤ p → p ≤ (3 : ℝ) / 2 →
    (∫ x in productBox I,
      Real.rpow (finiteSignedPartialMaximal I N (Finset.univ.erase j)
        (∑ Q ∈ partialInterior I N (Finset.univ.erase j),
          productDifferenceMap (Finset.univ.erase j) Q F) x) p) ≤
      (2 : ℝ) ^ (6 * (∑ i, d i) + 10) *
        ∫ x in productBox I,
          Real.rpow (finiteSquareFunction I N (Finset.univ.erase j) F x) p

def fibreSquareNormContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin (n + 1) → ℕ), (∀ i, 0 < d i) →
  ∀ (F : boundedMeasurableFunctions d), ProductLeafConstant I N F.1 →
    (∀ x, x ∉ productBox I → F.1 x = 0) →
  ∀ (j : Fin (n + 1)) (p : ℝ), 1 ≤ p → p ≤ (3 : ℝ) / 2 →
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteSignedPartialMaximal I N (Finset.univ.erase j)
        (∑ Q ∈ partialInterior I N (Finset.univ.erase j),
          productDifferenceMap (Finset.univ.erase j) Q F) x) p) (1 / p) ≤
      (2 : ℝ) ^ (6 * (∑ i, d i) + 10) *
        Real.rpow (∫ x in productBox I,
          Real.rpow (finiteSquareFunction I N (Finset.univ.erase j) F x) p) (1 / p)

end ReyZygmundVerification
