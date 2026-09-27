import ReyZygmund.Weighted.ProductStep
import ReyZygmund.Maximal.IteratedCoordinate

/-! Statements for lifting and iterating coordinate estimates. Signed inputs,
hypotheses on the top rectangle, real exponents and constants are written
independently of the theorem declarations.

-/

open BoxIntegral MeasureTheory ReyZygmund.Geometry
open scoped BigOperators Classical

namespace ReyZygmundVerification

noncomputable def productIntegralLiftingContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (H K : ProductPoint d → ℝ), ProductLeafConstant I N H → ProductLeafConstant I N K →
    (∀ x ∈ productBox I, 0 ≤ H x) → (∀ x ∈ productBox I, 0 ≤ K x) →
    ∀ (C : ℝ), 0 ≤ C → ∀ (j : Fin m),
    (∀ x ∈ productBox I,
      (∫ y in (I j : Set (Fin (d j) → ℝ)), H (Function.update x j y)) ≤
        C * (∫ y in (I j : Set (Fin (d j) → ℝ)), K (Function.update x j y))) →
    (∫ x in productBox I, H x) ≤ C * ∫ x in productBox I, K x

noncomputable def coordinateWeightedSquareContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (j : Fin m), 0 < d j → ∀ (u v : ProductPoint d → ℝ) (p : ℝ),
    1 < p → p ≤ 2 → ProductLeafConstant I N u → ProductLeafConstant I N v →
    (∀ x ∈ productBox I, 0 < v x) →
    (∑ Q ∈ interior (I j) (N j), ∫ x in productBox I,
      (coordinateDifference j Q u x) ^ 2 / Real.rpow (coordinateAverage j Q v x) (2 - p)) ≤
      Real.rpow 2 ((d j : ℝ) * (2 - p)) * ((3 - p) / (p - 1)) *
        ∫ x in productBox I, (u x) ^ 2 / Real.rpow (v x) (2 - p)

noncomputable def weightedProductStepContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f),
    (∀ x ∈ productBox I, 0 < f x) → ∀ (p : ℝ), 1 < p → p ≤ 2 →
    ∀ (B : Finset (Fin m)) (j : Fin m), j ∉ B → 0 < d j →
    ∀ (Q : ∀ i, Box (Fin (d i))), (∀ i ∈ B, Q i ∈ interior (I i) (N i)) →
    let F := finiteInput I N f hf
    let u := (productDifferenceMap B Q F).1
    let v := (productAverageMap B Q F).1
    (∑ R ∈ interior (I j) (N j), ∫ x in productBox I,
      (coordinateDifference j R u x) ^ 2 / Real.rpow (coordinateAverage j R v x) (2 - p)) ≤
      Real.rpow 2 ((d j : ℝ) * (2 - p)) * ((3 - p) / (p - 1)) *
        ∫ x in productBox I, (u x) ^ 2 / Real.rpow (v x) (2 - p)

noncomputable def coordinateMaximalIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (j : Fin m), 0 < d j → ∀ (f : ProductPoint d → ℝ), ProductLeafConstant I N f →
    ∀ (p : ℝ), 1 < p →
    (∫ x in productBox I, Real.rpow (ReyZygmund.coordinateDyadicMaximal j (I j) (N j) f x) p) ≤
      Real.rpow (p / (p - 1)) p * ∫ x in productBox I, Real.rpow |f x| p

noncomputable def iteratedCoordinateIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (order : List (Fin m)), (∀ i ∈ order, 0 < d i) →
    ∀ (f : ProductPoint d → ℝ), ProductLeafConstant I N f → ∀ (p : ℝ), 1 < p →
    (∫ x in productBox I,
      Real.rpow |(order.foldr (fun i g => ReyZygmund.coordinateDyadicMaximal i (I i) (N i) g) f) x| p) ≤
      Real.rpow (p / (p - 1)) (p * (order.length : ℝ)) *
        ∫ x in productBox I, Real.rpow |f x| p

end ReyZygmundVerification
