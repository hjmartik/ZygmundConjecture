import ReyZygmund.Weighted.ProjectedHolder

/-! Explicit expected Hölder application to the projected square. -/

open BoxIntegral MeasureTheory
open scoped BigOperators
open ReyZygmund ReyZygmund.Geometry ReyZygmund.Projection

namespace ReyZygmundVerification

def projectedHolderIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 0 < m →
  ∀ (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ), (∀ i, 0 < d i) →
  ∀ (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
  ∀ (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f),
    (∀ x ∈ productBox I, 0 < f x) →
  ∀ (p : ℝ), 1 < p → p ≤ 2 →
    let F := finiteInput I N f hf
    let W := finiteComplementSquareFunction I N (finiteProjectionMap I N G F)
    let M := finiteFamilyMaximal (averagingRectangles I N G) F
    let K := (m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)) / (p - 1) ^ (m - 1)
    (∫ x in productBox I, Real.rpow (W x) p) ≤
      Real.rpow (K * ∫ x in productBox I, Real.rpow (f x) p) (p / 2) *
        Real.rpow (∫ x in productBox I, Real.rpow (M x) p) (1 - p / 2)

def projectedHolderNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 0 < m →
  ∀ (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ), (∀ i, 0 < d i) →
  ∀ (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
  ∀ (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f),
    (∀ x ∈ productBox I, 0 < f x) →
  ∀ (p : ℝ), 1 < p → p ≤ 2 →
    let F := finiteInput I N f hf
    let W := finiteComplementSquareFunction I N (finiteProjectionMap I N G F)
    let M := finiteFamilyMaximal (averagingRectangles I N G) F
    let K := (m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)) / (p - 1) ^ (m - 1)
    Real.rpow (∫ x in productBox I, Real.rpow (W x) p) (1 / p) ≤
      Real.sqrt K * Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / 2 : ℝ) *
        Real.rpow (∫ x in productBox I, Real.rpow (M x) p) ((2 - p) / (2 * p))

end ReyZygmundVerification
