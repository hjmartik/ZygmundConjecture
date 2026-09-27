import ReyZygmund.Weighted.ProjectedHolderNorm

/-! Explicit norm-variable form of the finite projected Hölder estimate. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical
open ReyZygmund ReyZygmund.Geometry ReyZygmund.Projection

namespace ReyZygmundVerification

def projectedHolderNormVariablesContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 0 < m →
  ∀ (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ), (∀ i, 0 < d i) →
  ∀ (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
  ∀ (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f),
    (∀ x ∈ productBox I, 0 < f x) →
  ∀ (p : ℝ), 1 < p → p ≤ 2 →
    let F := finiteInput I N f hf
    let W := finiteComplementSquareFunction I N (finiteProjectionMap I N G F)
    let M := finiteFamilyMaximal (averagingRectangles I N G) F
    let X := Real.rpow (∫ x in productBox I, Real.rpow (M x) p) (1 / p)
    let Y := Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p)
    Real.rpow (∫ x in productBox I, Real.rpow (W x) p) (1 / p) ≤
      Real.sqrt ((m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1))) *
        Real.rpow (p - 1) (-((m - 1 : ℕ) : ℝ) / 2) *
        Real.rpow Y (p / 2) * Real.rpow X (1 - p / 2)

end ReyZygmundVerification
