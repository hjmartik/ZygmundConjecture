import ReyZygmund.Maximal.Represented

/-! Explicit finite maximal contracts, before any arbitrary-grid transfer. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical
open ReyZygmund ReyZygmund.Geometry ReyZygmund.Projection

namespace ReyZygmundVerification

def finiteAveragingMaximalNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m →
  ∀ (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ), (∀ i, 0 < d i) →
  ∀ (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
  ∀ (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f),
    (∀ x ∈ productBox I, 0 < f x) →
  ∀ (p : ℝ), 1 < p → p ≤ (3 : ℝ) / 2 →
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal (averagingRectangles I N G)
        (finiteInput I N f hf) x) p) (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p)

def finiteFamilyMonotonicityContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (G H : Finset (∀ i, Box (Fin (d i)))), G ⊆ H →
  ∀ (F : boundedMeasurableFunctions d) (x : ProductPoint d),
    finiteFamilyMaximal G F x ≤ finiteFamilyMaximal H F x

def finiteIncomparableMaximalNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m →
  ∀ (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ), (∀ i, 0 < d i) →
  ∀ (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
    (∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S) →
  ∀ (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f),
    (∀ x ∈ productBox I, 0 < f x) →
  ∀ (p : ℝ), 1 < p → p ≤ (3 : ℝ) / 2 →
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal G (finiteInput I N f hf) x) p) (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p)

end ReyZygmundVerification
