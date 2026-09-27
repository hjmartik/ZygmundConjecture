import ReyZygmund.Weighted.Product

/-! Statements of the finite product square estimate and the support identity equating
integrals on the top rectangle with the cylinder integrals in the paper.

-/

open BoxIntegral MeasureTheory ReyZygmund.Geometry
open scoped BigOperators Classical

namespace ReyZygmundVerification

noncomputable def productEnergyCylinderContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (A : Finset (Fin m)) (Q : ∀ i, Box (Fin (d i))),
    Q ∈ partialInterior I N A → ∀ (p : ℝ),
    let F := finiteInput I N f hf
    (∫ x in productBox I, ((productDifferenceMap A Q F).1 x) ^ 2 /
      Real.rpow ((productAverageMap A Q F).1 x) (2 - p)) =
    ∫ x in productBox Q, ((productDifferenceMap A Q F).1 x) ^ 2 /
      Real.rpow ((productAverageMap A Q F).1 x) (2 - p)

noncomputable def productWeightedSquareContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f),
    (∀ x ∈ productBox I, 0 < f x) → ∀ (p : ℝ), 1 < p → p ≤ 2 →
    ∀ (A : Finset (Fin m)), (∀ i ∈ A, 0 < d i) →
    let F := finiteInput I N f hf
    (∑ Q ∈ partialInterior I N A, ∫ x in productBox I,
      ((productDifferenceMap A Q F).1 x) ^ 2 /
        Real.rpow ((productAverageMap A Q F).1 x) (2 - p)) ≤
      Real.rpow 2 ((2 - p) * (∑ i ∈ A, (d i : ℝ))) *
        ((3 - p) / (p - 1)) ^ A.card *
          ∫ x in productBox I, Real.rpow (f x) p

end ReyZygmundVerification
