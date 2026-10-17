import ReyZygmund.Weighted.EnergyHolder

/-! The weighted Hölder statement on the top rectangle, with coefficient one. -/

open BoxIntegral MeasureTheory ReyZygmund.Geometry

namespace ReyZygmundVerification

noncomputable def weightedEnergyHolderContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (U V : ProductPoint d → ℝ),
    ProductLeafConstant I N U → ProductLeafConstant I N V →
    (∀ x ∈ productRectangle I, 0 ≤ U x) → (∀ x ∈ productRectangle I, 0 < V x) →
    ∀ (p : ℝ), 1 < p → p ≤ 2 →
    (∫ x in productRectangle I, Real.rpow (U x) p) ≤
      Real.rpow (∫ x in productRectangle I, (U x) ^ 2 / Real.rpow (V x) (2 - p)) (p / 2) *
        Real.rpow (∫ x in productRectangle I, Real.rpow (V x) p) (1 - p / 2)

end ReyZygmundVerification
