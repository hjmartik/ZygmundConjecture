import ReyZygmund.Geometry.ProductMean
import ReyZygmund.Maximal.FamilyProperties
import ReyZygmund.Weighted.CrossProductStep
import ReyZygmund.Geometry.ProductL2

/-!
Expected propositions for product integration, the ordinary finite
maximal bounds, averaged denominators, and the finite energy identities.
Each proposition is explicit; no candidate theorem is used as its definition.
-/

open BoxIntegral MeasureTheory ReyZygmund.Geometry ReyZygmund.Projection
open scoped BigOperators Classical

namespace ReyZygmundVerification

noncomputable def productMeanContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (Q : ∀ i, Box (Fin (d i)))
    (F : boundedMeasurableFunctions d) (x : ProductPoint d),
    (productAverageMap Finset.univ Q F).1 x =
      (productBox Q).indicator
        (fun _ => (∫ y in productBox Q, F.1 y) / volume.real (productBox Q)) x

noncomputable def productMaximalIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A : Finset (Fin m)), (∀ i ∈ A, 0 < d i) →
    ∀ (F : boundedMeasurableFunctions d), ProductLeafConstant I N F.1 →
    (∀ x, x ∉ productBox I → F.1 x = 0) → ∀ (p : ℝ), 1 < p →
    (∫ x in productBox I, Real.rpow (ReyZygmund.finiteProductMaximal I N A F x) p) ≤
      Real.rpow (p / (p - 1)) (p * (A.card : ℝ)) *
        ∫ x in productBox I, Real.rpow |F.1 x| p

noncomputable def familyMaximalMeasurableContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i))))
    (F : boundedMeasurableFunctions d), Measurable (ReyZygmund.finiteFamilyMaximal G F)

noncomputable def familyMaximalIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
    (∀ i, 0 < d i) → ∀ (F : boundedMeasurableFunctions d),
    ProductLeafConstant I N F.1 → (∀ x, x ∉ productBox I → F.1 x = 0) →
    ∀ (p : ℝ), 1 < p →
    (∫ x in productBox I, Real.rpow (ReyZygmund.finiteFamilyMaximal G F x) p) ≤
      Real.rpow (p / (p - 1)) (p * (m : ℝ)) *
        ∫ x in productBox I, Real.rpow |F.1 x| p

noncomputable def averagedDenominatorIdentityContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
    ∀ (j : Fin m) (Q : ∀ i, Box (Fin (d i))) (P : Box (Fin (d j))),
    P ∈ partitionCubes (I j) (N j) (eligibleProjections j G Q) →
    ∀ (F : boundedMeasurableFunctions d) (x : ProductPoint d), x j ∈ P →
    coordinateCrossAverage j (I j) (N j) (eligibleProjections j G Q)
      (productAverageMap (Finset.univ.erase j) Q F).1 x =
        (productAverageMap Finset.univ (Function.update Q j P) F).1 x

noncomputable def averagedDenominatorBoundContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
    ∀ (F : boundedMeasurableFunctions d), (∀ y ∈ productBox I, 0 ≤ F.1 y) →
    ∀ (j : Fin m) (Q : ∀ i, Box (Fin (d i))),
    (∀ i, i ≠ j → Q i ∈ descendants (I i) (N i)) →
    ∀ (x : ProductPoint d), x j ∈ I j →
    coordinateCrossAverage j (I j) (N j) (eligibleProjections j G Q)
      (productAverageMap (Finset.univ.erase j) Q F).1 x ≤
        ReyZygmund.finiteFamilyMaximal (averagingRectangles I N G) F x

noncomputable def averagingFamilyMaximalPositiveContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 0 < m →
    ∀ (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
    ∀ (F : boundedMeasurableFunctions d), (∀ y ∈ productBox I, 0 < F.1 y) →
    ∀ (x : ProductPoint d), x ∈ productBox I →
    0 < ReyZygmund.finiteFamilyMaximal (averagingRectangles I N G) F x

noncomputable def weightedCrossProductContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f),
    (∀ x ∈ productBox I, 0 < f x) → ∀ (p : ℝ), 1 < p → p ≤ 2 →
    ∀ (B : Finset (Fin m)) (j : Fin m), j ∉ B →
    ∀ (Q : ∀ i, Box (Fin (d i))), (∀ i ∈ B, Q i ∈ interior (I i) (N i)) →
    ∀ (eligible : Finset (Box (Fin (d j)))), eligible ⊆ descendants (I j) (N j) →
    let F := finiteInput I N f hf
    let u := (productDifferenceMap B Q F).1
    let v := (productAverageMap B Q F).1
    (∫ x in productBox I,
      (coordinateCrossAverage j (I j) (N j) eligible u x) ^ 2 /
        Real.rpow (coordinateCrossAverage j (I j) (N j) eligible v x) (2 - p)) ≤
      ∫ x in productBox I, (u x) ^ 2 / Real.rpow (v x) (2 - p)

noncomputable def productDifferenceIntegralOrthogonalityContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ i, 0 < d i) → ∀ (F : boundedMeasurableFunctions d)
    (L Q : ∀ i, Box (Fin (d i))), L ∈ productInterior I N →
    Q ∈ productInterior I N → L ≠ Q →
    (∫ x in productBox I, (productDifferenceMap Finset.univ L F).1 x *
      (productDifferenceMap Finset.univ Q F).1 x) = 0

noncomputable def productDifferenceSquareIdentityContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ i, 0 < d i) → ∀ (F : boundedMeasurableFunctions d)
    (H : Finset (∀ i, Box (Fin (d i)))), H ⊆ productInterior I N →
    (∫ x in productBox I, (∑ Q ∈ H, (productDifferenceMap Finset.univ Q F).1 x) ^ 2) =
      ∑ Q ∈ H, ∫ x in productBox I, ((productDifferenceMap Finset.univ Q F).1 x) ^ 2

end ReyZygmundVerification
