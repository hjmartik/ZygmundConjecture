import ReyZygmund.Maximal.RepresentationBound

/-! Explicit expected signed partial-coordinate interfaces. -/

open BoxIntegral MeasureTheory
open scoped BigOperators
open ReyZygmund ReyZygmund.Geometry ReyZygmund.Projection

namespace ReyZygmundVerification

def partialSignedMeasurabilityContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A : Finset (Fin m)) (F : boundedMeasurableFunctions d),
    Measurable (finiteSignedPartialMaximal I N A F)

def partialSignedMonotonicityContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d), ProductLeafConstant I N F.1 →
    (∀ x, x ∉ productBox I → F.1 x = 0) →
  ∀ (B A : Finset (Fin m)), B ⊆ A →
  ∀ (x : ProductPoint d), x ∈ productBox I →
    finiteSignedPartialMaximal I N B F x ≤ finiteSignedPartialMaximal I N A F x

def representationMaximalContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ), (∀ i, 0 < d i) →
  ∀ (G : Finset (∀ i, Box (Fin (d i)))) (f : boundedMeasurableFunctions d),
    ProductLeafConstant I N f.1 → (∀ x, x ∉ productBox I → f.1 x = 0) →
    (∀ x ∈ productBox I, 0 ≤ f.1 x) →
  ∀ (x : ProductPoint d), x ∈ productBox I →
    finiteFamilyMaximal (averagingRectangles I N G) f x ≤
      (2 : ℝ) ^ m * ∑ j,
        finiteSignedPartialMaximal I N (Finset.univ.erase j)
          (finiteProjectionMap I N G f) x

end ReyZygmundVerification
