import ReyZygmund.Maximal.UpperExponent

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry ReyZygmund.Projection

def finiteUpperExponentNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 1 ≤ m →
  ∀ (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
  (∀ i, 0 < d i) →
  ∀ (F : boundedMeasurableFunctions d), ProductLeafConstant I N F.1 →
    (∀ x, x ∉ productBox I → F.1 x = 0) →
  ∀ (p : ℝ), (3 : ℝ) / 2 ≤ p →
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal G F x) p) (1 / p) ≤
      3 * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow |F.1 x| p) (1 / p)

end ReyZygmundVerification
