import ReyZygmund.Maximal.WeakerRepresentation

/-! Expected union representation under the paper's weaker containment condition. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical
open ReyZygmund ReyZygmund.Geometry ReyZygmund.Projection

namespace ReyZygmundVerification

def weakerRepresentationContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ), (∀ i, 0 < d i) →
  ∀ (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
    (∀ R ∈ G, ∀ J ∈ G, (∀ i, R i ≤ J i) → ∃ i, R i = J i) →
  ∀ (R : ∀ i, Box (Fin (d i))), R ∈ G ∪ averagingRectangles I N G →
  ∀ (F : boundedMeasurableFunctions d), ProductLeafConstant I N F.1 →
    (∀ x, x ∉ productBox I → F.1 x = 0) →
  ∀ (x : ProductPoint d), x ∈ productBox R →
    (productAverageMap Finset.univ R F).1 x =
      ∑ A ∈ ((Finset.univ : Finset (Fin m)).powerset.erase Finset.univ),
        (-1 : ℝ) ^ (m + 1 + A.card) *
          (productAverageMap A R (finiteProjectionMap I N G F)).1 x

def weakerRepresentationMaximalContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ), (∀ i, 0 < d i) →
  ∀ (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
    (∀ R ∈ G, ∀ J ∈ G, (∀ i, R i ≤ J i) → ∃ i, R i = J i) →
  ∀ (f : boundedMeasurableFunctions d), ProductLeafConstant I N f.1 →
    (∀ x, x ∉ productBox I → f.1 x = 0) →
    (∀ x ∈ productBox I, 0 ≤ f.1 x) →
  ∀ (x : ProductPoint d), x ∈ productBox I →
    finiteFamilyMaximal (G ∪ averagingRectangles I N G) f x ≤
      (2 : ℝ) ^ m * ∑ j,
        finiteSignedPartialMaximal I N (Finset.univ.erase j)
          (finiteProjectionMap I N G f) x

end ReyZygmundVerification
