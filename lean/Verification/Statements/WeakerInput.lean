import ReyZygmund.Maximal.WeakerInput

/-! Explicit propositions for weaker-containment input reductions.
Independent mathematical review is separate from the type comparison. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry ReyZygmund.Projection

def weakerNonnegativeMaximalNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m →
  ∀ (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ), (∀ i, 0 < d i) →
  ∀ (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
  (∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → ∃ i, R i = S i) →
  ∀ (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f),
  (∀ x ∈ productBox I, 0 ≤ f x) →
  ∀ (p : ℝ), 1 < p → p ≤ (3 : ℝ) / 2 →
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal G (finiteInput I N f hf) x) p) (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p)

def weakerGeneralInputNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m →
  ∀ (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ), (∀ i, 0 < d i) →
  ∀ (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
  (∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → ∃ i, R i = S i) →
  ∀ (f : ProductPoint d → ℝ) (p : ℝ), 1 < p →
  IntegrableOn f (productBox I) volume →
  IntegrableOn (fun x => Real.rpow |f x| p) (productBox I) volume →
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFunctionMaximal G f x) p) (1 / p) ≤
      (maximalDimensionConstant d + 3) * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow |f x| p) (1 / p)

end ReyZygmundVerification
