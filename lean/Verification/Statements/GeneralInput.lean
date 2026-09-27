import ReyZygmund.Maximal.GeneralInput

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry ReyZygmund.Projection

def finiteFunctionMaximalBoundedContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i))))
    (F : boundedMeasurableFunctions d),
    finiteFunctionMaximal G F.1 = finiteFamilyMaximal G F

def finiteFunctionMaximalAveragingContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i)))
    (N : Fin m → ℕ) (G : Finset (∀ i, Box (Fin (d i)))),
  G ⊆ productDescendants I N →
  ∀ (f : ProductPoint d → ℝ), IntegrableOn f (productBox I) volume →
    finiteFunctionMaximal G f = finiteFamilyMaximal G
      (finiteInput I N (leafAverage I N (fun x => |f x|))
        (productLeafConstant_leafAverage I N (fun x => |f x|)))

def finiteGeneralInputNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m →
  ∀ (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ), (∀ i, 0 < d i) →
  ∀ (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
  (∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S) →
  ∀ (f : ProductPoint d → ℝ) (p : ℝ), 1 < p →
  IntegrableOn f (productBox I) volume →
  IntegrableOn (fun x => Real.rpow |f x| p) (productBox I) volume →
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFunctionMaximal G f x) p) (1 / p) ≤
      (maximalDimensionConstant d + 3) * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow |f x| p) (1 / p)

end ReyZygmundVerification
