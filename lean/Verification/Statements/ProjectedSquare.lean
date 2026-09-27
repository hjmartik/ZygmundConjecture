import ReyZygmund.Weighted.Projected

/-!
Explicit expected propositions for the projected weighted-square estimate.
The denominator is the averaging-family maximal function, and the
input's positivity is restricted to the top rectangle.
-/

open BoxIntegral MeasureTheory ReyZygmund.Geometry ReyZygmund.Projection
open scoped BigOperators Classical

namespace ReyZygmundVerification

noncomputable def projectedRowEnergyContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ i, 0 < d i) → ∀ (G : Finset (∀ i, Box (Fin (d i)))),
    G ⊆ productDescendants I N →
    ∀ (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f),
    (∀ x ∈ productBox I, 0 < f x) → ∀ (p : ℝ), 1 < p → p ≤ 2 →
    ∀ (j : Fin m) (Q : ∀ i, Box (Fin (d i))),
    (∀ i, i ≠ j → Q i ∈ interior (I i) (N i)) →
    let F := finiteInput I N f hf
    (∫ x in productBox I,
      ((productDifferenceMap (Finset.univ.erase j) Q
        (finiteProjectionMap I N G F)).1 x) ^ 2 /
        Real.rpow (ReyZygmund.finiteFamilyMaximal (averagingRectangles I N G) F x)
          (2 - p)) ≤
      ∫ x in productBox I, ((productDifferenceMap (Finset.univ.erase j) Q F).1 x) ^ 2 /
        Real.rpow ((productAverageMap (Finset.univ.erase j) Q F).1 x) (2 - p)

noncomputable def projectedWeightedSquareExactContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ i, 0 < d i) → ∀ (G : Finset (∀ i, Box (Fin (d i)))),
    G ⊆ productDescendants I N →
    ∀ (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f),
    (∀ x ∈ productBox I, 0 < f x) → ∀ (p : ℝ), 1 < p → p ≤ 2 →
    let F := finiteInput I N f hf
    (∫ x in productBox I,
      (finiteComplementSquareFunction I N (finiteProjectionMap I N G F) x) ^ 2 /
        Real.rpow (ReyZygmund.finiteFamilyMaximal (averagingRectangles I N G) F x)
          (2 - p)) ≤
      (∑ j : Fin m,
        Real.rpow 2 ((2 - p) * ∑ i ∈ Finset.univ.erase j, (d i : ℝ)) *
          ((3 - p) / (p - 1)) ^ (Finset.univ.erase j).card) *
        ∫ x in productBox I, Real.rpow (f x) p

noncomputable def projectedWeightedSquareContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ i, 0 < d i) → ∀ (G : Finset (∀ i, Box (Fin (d i)))),
    G ⊆ productDescendants I N →
    ∀ (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f),
    (∀ x ∈ productBox I, 0 < f x) → ∀ (p : ℝ), 1 < p → p ≤ 2 →
    let F := finiteInput I N f hf
    (∫ x in productBox I,
      (finiteComplementSquareFunction I N (finiteProjectionMap I N G F) x) ^ 2 /
        Real.rpow (ReyZygmund.finiteFamilyMaximal (averagingRectangles I N G) F x)
          (2 - p)) ≤
      ((m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)) / (p - 1) ^ (m - 1)) *
        ∫ x in productBox I, Real.rpow (f x) p

end ReyZygmundVerification
