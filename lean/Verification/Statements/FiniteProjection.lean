import ReyZygmund.Projection.CommonProjection

/-!
Expected propositions for the finite operator algebra and projection.
These spell out the reviewed statements; none is an alias for a candidate
theorem's type. Full-grid cutoff conversion is outside this finite contract.
-/

open BoxIntegral MeasureTheory ReyZygmund.Geometry ReyZygmund.Projection
open scoped BigOperators Classical

namespace ReyZygmundVerification

noncomputable def finiteAverageDifferenceContract : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (I : Box (Fin d)) (N : ℕ) (L Q : Box (Fin d)),
    L ∈ descendants I N → Q ∈ descendants I N → ∀ (f : (Fin d → ℝ) → ℝ),
    IntegrableOn f (I : Set (Fin d → ℝ)) volume →
    boxAverage L (boxDifference Q f) =
      if L < Q then (L : Set (Fin d → ℝ)).indicator (boxDifference Q f) else 0

noncomputable def finiteDifferenceDifferenceContract : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (I : Box (Fin d)) (N : ℕ) (L Q : Box (Fin d)),
    L ∈ descendants I N → Q ∈ descendants I N → ∀ (f : (Fin d → ℝ) → ℝ),
    IntegrableOn f (I : Set (Fin d → ℝ)) volume →
    boxDifference L (boxDifference Q f) = if L = Q then boxDifference Q f else 0

noncomputable def productDifferenceOrthogonalityContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ i, 0 < d i) → ∀ (A : Finset (Fin m)) (K L : ∀ i, Box (Fin (d i))),
    (∀ i ∈ A, K i ∈ descendants (I i) (N i)) →
    (∀ i, L i ∈ descendants (I i) (N i)) →
    productDifferenceMap A K * productDifferenceMap Finset.univ L =
      if ∀ i ∈ A, K i = L i then productDifferenceMap Finset.univ L else 0

noncomputable def productAverageDifferenceZeroContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A : Finset (Fin m)) (K L : ∀ i, Box (Fin (d i))),
    (∀ i ∈ A, K i ∈ descendants (I i) (N i)) →
    (∀ i, L i ∈ descendants (I i) (N i)) →
    (∃ i ∈ A, 0 < d i ∧ ¬ K i < L i) →
    productAverageMap A K * productDifferenceMap Finset.univ L = 0

noncomputable def productDifferenceClosureContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : boundedMeasurableFunctions d), ProductLeafConstant I N f.1 →
    (∀ x, x ∉ productBox I → f.1 x = 0) →
    ∀ (A : Finset (Fin m)) (Q : ∀ i, Box (Fin (d i))),
    (∀ i ∈ A, Q i ∈ interior (I i) (N i)) →
    ProductLeafConstant I N (productDifferenceMap A Q f).1 ∧
      ∀ x, x ∉ productBox I → (productDifferenceMap A Q f).1 x = 0

noncomputable def crossCoordinateDefinitionContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (i : Fin m) (I : Box (Fin (d i))) (N : ℕ)
    (eligible : Finset (Box (Fin (d i)))) (f : ProductPoint d → ℝ),
    coordinateCrossAverage i I N eligible f =
      ∑ P ∈ partitionCubes I N eligible, coordinateAverage i P f

noncomputable def crossCoordinateMeasurabilityContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (i : Fin m) (I : Box (Fin (d i))) (N : ℕ)
    (eligible : Finset (Box (Fin (d i)))) (f : ProductPoint d → ℝ),
    Measurable f → Measurable (coordinateCrossAverage i I N eligible f)

noncomputable def crossCoordinateIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (i : Fin m) (I : Box (Fin (d i))) (N : ℕ)
    (eligible : Finset (Box (Fin (d i)))), eligible ⊆ descendants I N →
    ∀ (f : ProductPoint d → ℝ) (x : ProductPoint d),
    IntegrableOn (fun y => f (Function.update x i y)) (I : Set (Fin (d i) → ℝ)) volume →
    Integrable (fun y => coordinateCrossAverage i I N eligible f (Function.update x i y))
      volume ∧
      (∫ y, coordinateCrossAverage i I N eligible f (Function.update x i y)) =
        ∫ y in (I : Set (Fin (d i) → ℝ)), f (Function.update x i y)

noncomputable def crossCoordinateClosureContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ), ProductLeafConstant I N f →
    (∀ x, x ∉ productBox I → f x = 0) →
    ∀ (i : Fin m) (eligible : Finset (Box (Fin (d i)))),
    eligible ⊆ descendants (I i) (N i) →
    ProductLeafConstant I N (coordinateCrossAverage i (I i) (N i) eligible f) ∧
      ∀ x, x ∉ productBox I → coordinateCrossAverage i (I i) (N i) eligible f x = 0

noncomputable def crossCoordinateComplementContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ), ProductLeafConstant I N f →
    ∀ (i : Fin m), 0 < d i → ∀ (eligible : Finset (Box (Fin (d i)))),
    eligible ⊆ descendants (I i) (N i) →
    (productBox I).indicator f -
        coordinateCrossAverage i (I i) (N i) eligible ((productBox I).indicator f) =
      ∑ L ∈ (interior (I i) (N i)).filter (fun L => ∃ J ∈ eligible, L ≤ J),
        coordinateDifference i L ((productBox I).indicator f)

noncomputable def finiteProjectionFormulaContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (f : boundedMeasurableFunctions d),
    (finiteProjectionMap I N G f).1 =
      f.1 - ∑ L ∈ removedIndices I N G, (productDifferenceMap Finset.univ L f).1

noncomputable def rootAverageProjectionContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (i : Fin m), 0 < d i →
    averageMap i (I i) * finiteProjectionMap I N G = averageMap i (I i)

noncomputable def removedDifferenceProjectionContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ i, 0 < d i) → ∀ (G : Finset (∀ i, Box (Fin (d i)))) (K : ∀ i, Box (Fin (d i))),
    K ∈ removedIndices I N G →
    productDifferenceMap Finset.univ K * finiteProjectionMap I N G = 0

noncomputable def projectionClosureContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (f : boundedMeasurableFunctions d),
    ProductLeafConstant I N f.1 → (∀ x, x ∉ productBox I → f.1 x = 0) →
    ProductLeafConstant I N (finiteProjectionMap I N G f).1 ∧
      ∀ x, x ∉ productBox I → (finiteProjectionMap I N G f).1 x = 0

noncomputable def finiteCrossProjectionContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ i, 0 < d i) → ∀ (G : Finset (∀ i, Box (Fin (d i)))),
    (∀ J ∈ G, ∀ i, J i ∈ descendants (I i) (N i)) →
    ∀ (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
      (j : Fin m) (K : ∀ i, Box (Fin (d i))),
    (∀ i, i ≠ j → K i ∈ interior (I i) (N i)) →
    (productDifferenceMap (Finset.univ.erase j) K
      (finiteProjectionMap I N G (finiteInput I N f hf))).1 =
        coordinateCrossAverage j (I j) (N j) (eligibleProjections j G K)
          (productDifferenceMap (Finset.univ.erase j) K (finiteInput I N f hf)).1

end ReyZygmundVerification
