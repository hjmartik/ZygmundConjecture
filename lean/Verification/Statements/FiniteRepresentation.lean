import ReyZygmund.Projection.Representation

/-!
Expected propositions for preserved finite averages and their signed local
representation. These do not assume incomparability or original membership
in the averaging family, except where separately stated in geometric results.
-/

open BoxIntegral ReyZygmund.Geometry ReyZygmund.Projection
open scoped BigOperators Classical

namespace ReyZygmundVerification

noncomputable def averagingPreservationContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ i, 0 < d i) → ∀ (G : Finset (∀ i, Box (Fin (d i)))) (R : ∀ i, Box (Fin (d i))),
    R ∈ averagingRectangles I N G →
    productAverageMap Finset.univ R * finiteProjectionMap I N G = productAverageMap Finset.univ R

noncomputable def originalPreservationContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ i, 0 < d i) → ∀ (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
    (∀ R ∈ G, ∀ J ∈ G, ¬ ∀ i, R i < J i) →
    ∀ (R : ∀ i, Box (Fin (d i))), R ∈ G →
    productAverageMap Finset.univ R * finiteProjectionMap I N G = productAverageMap Finset.univ R

noncomputable def localProductExpansionContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ i, 0 < d i) → ∀ (R : ∀ i, Box (Fin (d i))),
    (∀ i, R i ∈ descendants (I i) (N i)) →
    ∀ (F : boundedMeasurableFunctions d), ProductLeafConstant I N F.1 →
    (∀ x, x ∉ productBox I → F.1 x = 0) → ∀ (x : ProductPoint d), x ∈ productBox R →
    (∑ L ∈ (productInterior I N).filter (fun L => ∀ i, L i ≤ R i),
      (productDifferenceMap Finset.univ L F).1 x) =
      ∑ B ∈ (Finset.univ : Finset (Fin m)).powerset,
        (-1 : ℝ) ^ B.card * (productAverageMap B R F).1 x

noncomputable def finiteRepresentationContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ i, 0 < d i) → ∀ (G : Finset (∀ i, Box (Fin (d i)))) (R : ∀ i, Box (Fin (d i))),
    R ∈ averagingRectangles I N G →
    ∀ (F : boundedMeasurableFunctions d), ProductLeafConstant I N F.1 →
    (∀ x, x ∉ productBox I → F.1 x = 0) → ∀ (x : ProductPoint d), x ∈ productBox R →
    (productAverageMap Finset.univ R F).1 x =
      ∑ B ∈ ((Finset.univ : Finset (Fin m)).powerset.erase Finset.univ),
        (-1 : ℝ) ^ (m + 1 + B.card) *
          (productAverageMap B R (finiteProjectionMap I N G F)).1 x

end ReyZygmundVerification
