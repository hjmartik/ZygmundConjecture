import ReyZygmund.Maximal.WeakerBound

/-! Finite strict-positive maximal bounds under weaker containment. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical
open ReyZygmund ReyZygmund.Geometry ReyZygmund.Projection

namespace ReyZygmundVerification

def weakerUnionMaximalNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m →
  ∀ (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ), (∀ i, 0 < d i) →
  ∀ (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
    (∀ R ∈ G, ∀ J ∈ G, (∀ i, R i ≤ J i) → ∃ i, R i = J i) →
  ∀ (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f),
    (∀ x ∈ productBox I, 0 < f x) →
  ∀ (p : ℝ), 1 < p → p ≤ (3 : ℝ) / 2 →
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal (G ∪ averagingRectangles I N G)
        (finiteInput I N f hf) x) p) (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p)

def weakerMaximalNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m →
  ∀ (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ), (∀ i, 0 < d i) →
  ∀ (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
    (∀ R ∈ G, ∀ J ∈ G, (∀ i, R i ≤ J i) → ∃ i, R i = J i) →
  ∀ (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f),
    (∀ x ∈ productBox I, 0 < f x) →
  ∀ (p : ℝ), 1 < p → p ≤ (3 : ℝ) / 2 →
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal G (finiteInput I N f hf) x) p) (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p)

end ReyZygmundVerification
