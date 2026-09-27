import ReyZygmund.Maximal.Square

/-!
Explicit expected propositions for the finite signed maximal-square argument.
The distribution is for the difference sum; the final input estimate
retains the reconstruction hypothesis and closed real-exponent interval.
-/

open BoxIntegral MeasureTheory ReyZygmund.Geometry ReyZygmund.Projection
open scoped BigOperators Classical

namespace ReyZygmundVerification

noncomputable def finiteSquareDistributionContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ i, 0 < d i) → ∀ (F : boundedMeasurableFunctions d),
    ProductLeafConstant I N F.1 → (∀ x, x ∉ productBox I → F.1 x = 0) → ∀ (n : ℤ),
    volume.real {x | x ∈ productBox I ∧ Real.rpow 2 (n : ℝ) <
      ReyZygmund.finiteSignedProductMaximal I N
        (∑ Q ∈ productInterior I N, productDifferenceMap Finset.univ Q F) x} ≤
      (2 : ℝ) ^ (6 * (∑ i, d i) + 5) *
        (volume.real (ReyZygmund.finiteSquareLevelSet I N F n) + Real.rpow 2 (-2 * (n : ℝ)) *
          ∑' j : ℤ, if j < n then Real.rpow 2 (2 * (j : ℝ)) *
            volume.real (ReyZygmund.finiteSquareLevelSet I N F j) else 0)

noncomputable def finiteDifferenceSumSquareIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ i, 0 < d i) → ∀ (F : boundedMeasurableFunctions d),
    ProductLeafConstant I N F.1 → (∀ x, x ∉ productBox I → F.1 x = 0) →
    ∀ (p : ℝ), 1 ≤ p → p ≤ (3 : ℝ) / 2 →
    (∫ x in productBox I,
      Real.rpow (ReyZygmund.finiteSignedProductMaximal I N
        (∑ Q ∈ productInterior I N, productDifferenceMap Finset.univ Q F) x) p) ≤
      (2 : ℝ) ^ (6 * (∑ i, d i) + 10) *
        ∫ x in productBox I, Real.rpow (finiteSquareFunction I N Finset.univ F x) p

noncomputable def finiteSignedSquareIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ i, 0 < d i) → ∀ (F : boundedMeasurableFunctions d),
    ProductLeafConstant I N F.1 → (∀ x, x ∉ productBox I → F.1 x = 0) →
    F = (∑ Q ∈ productInterior I N, productDifferenceMap Finset.univ Q F) →
    ∀ (p : ℝ), 1 ≤ p → p ≤ (3 : ℝ) / 2 →
    (∫ x in productBox I, Real.rpow (ReyZygmund.finiteSignedProductMaximal I N F x) p) ≤
      (2 : ℝ) ^ (6 * (∑ i, d i) + 10) *
        ∫ x in productBox I, Real.rpow (finiteSquareFunction I N Finset.univ F x) p

noncomputable def finiteSignedSquareLpContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ i, 0 < d i) → ∀ (F : boundedMeasurableFunctions d),
    ProductLeafConstant I N F.1 → (∀ x, x ∉ productBox I → F.1 x = 0) →
    F = (∑ Q ∈ productInterior I N, productDifferenceMap Finset.univ Q F) →
    ∀ (p : ℝ), 1 ≤ p → p ≤ (3 : ℝ) / 2 →
    Real.rpow (∫ x in productBox I,
      Real.rpow (ReyZygmund.finiteSignedProductMaximal I N F x) p) (1 / p) ≤
      (2 : ℝ) ^ (6 * (∑ i, d i) + 10) *
        Real.rpow (∫ x in productBox I,
          Real.rpow (finiteSquareFunction I N Finset.univ F x) p) (1 / p)

end ReyZygmundVerification
