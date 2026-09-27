import ReyZygmund.Maximal.FiniteGrid

open BoxIntegral MeasureTheory
open scoped Classical

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry

def finiteGridMaximalIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m → (∀ i, 0 < d i) →
  ∀ (D : ∀ i, DyadicGrid (d i)) (G : Finset (∀ i, Box (Fin (d i)))),
  ↑G ⊆ gridRectangles D →
  (∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S) →
  ∀ (f : ProductPoint d → ℝ) (p : ℝ), 1 < p →
  MemLp f (ENNReal.ofReal p) volume →
    (∫ x, Real.rpow (finiteFunctionMaximal G f x) p) ≤
      Real.rpow ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1)) p * ∫ x, Real.rpow |f x| p

def finiteGridMaximalNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m → (∀ i, 0 < d i) →
  ∀ (D : ∀ i, DyadicGrid (d i)) (G : Finset (∀ i, Box (Fin (d i)))),
  ↑G ⊆ gridRectangles D →
  (∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S) →
  ∀ (f : ProductPoint d → ℝ) (p : ℝ), 1 < p →
  MemLp f (ENNReal.ofReal p) volume →
    Real.rpow (∫ x, Real.rpow (finiteFunctionMaximal G f x) p) (1 / p) ≤
      (maximalDimensionConstant d + 3) * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x, Real.rpow |f x| p) (1 / p)

end ReyZygmundVerification
