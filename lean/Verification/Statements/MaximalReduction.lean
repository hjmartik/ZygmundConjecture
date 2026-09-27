import ReyZygmund.Maximal.Reduction

/-! Explicit finite representation-to-norm and maximal-to-square contracts. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical
open ReyZygmund ReyZygmund.Geometry ReyZygmund.Projection

namespace ReyZygmundVerification

def representationMaximalNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ), (∀ i, 0 < d i) →
  ∀ (G : Finset (∀ i, Box (Fin (d i)))) (f : boundedMeasurableFunctions d),
    ProductLeafConstant I N f.1 →
    (∀ x, x ∉ productBox I → f.1 x = 0) →
    (∀ x ∈ productBox I, 0 ≤ f.1 x) →
  ∀ (p : ℝ), 1 ≤ p →
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal (averagingRectangles I N G) f x) p) (1 / p) ≤
      (2 : ℝ) ^ m * ∑ j,
        Real.rpow (∫ x in productBox I,
          Real.rpow (finiteSignedPartialMaximal I N (Finset.univ.erase j)
            (finiteProjectionMap I N G f) x) p) (1 / p)

def finiteMaximalToSquareContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m →
  ∀ (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ), (∀ i, 0 < d i) →
  ∀ (G : Finset (∀ i, Box (Fin (d i)))) (f : boundedMeasurableFunctions d),
    ProductLeafConstant I N f.1 →
    (∀ x, x ∉ productBox I → f.1 x = 0) →
    (∀ x ∈ productBox I, 0 ≤ f.1 x) →
  ∀ (p : ℝ), 1 < p → p ≤ (3 : ℝ) / 2 →
    let C := (m : ℝ) * (2 : ℝ) ^ m *
      ((2 : ℝ) ^ (6 * (∑ i, d i) + 10) + (2 : ℝ) ^ (m - 1))
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal (averagingRectangles I N G) f x) p) (1 / p) ≤
      C * (p / (p - 1)) ^ (m - 2) *
        Real.rpow (∫ x in productBox I, Real.rpow |f.1 x| p) (1 / p) +
      C * Real.rpow (∫ x in productBox I,
        Real.rpow (finiteComplementSquareFunction I N (finiteProjectionMap I N G f) x) p)
        (1 / p)

end ReyZygmundVerification
