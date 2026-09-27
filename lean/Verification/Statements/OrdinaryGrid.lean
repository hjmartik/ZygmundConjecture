import ReyZygmund.Maximal.OrdinaryGrid

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry ReyZygmund.Projection

def finiteOrdinaryInputIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ i, 0 < d i) →
    ∀ G : Finset (∀ i, Box (Fin (d i))), G ⊆ productDescendants I N →
    ∀ (f : ProductPoint d → ℝ) (p : ℝ), 1 < p →
    IntegrableOn f (productBox I) volume →
    IntegrableOn (fun x => Real.rpow |f x| p) (productBox I) volume →
    (∫ x in productBox I, Real.rpow (finiteFunctionMaximal G f x) p) ≤
      Real.rpow (p / (p - 1)) (p * (m : ℝ)) *
        ∫ x in productBox I, Real.rpow |f x| p

def finiteOrdinaryGridSquareContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (G : Finset (∀ i, Box (Fin (d i)))),
    (↑G : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D →
    ∀ f : ProductPoint d → ℝ, MemLp f 2 volume →
    (∫ x, (finiteFunctionMaximal G f x) ^ 2) ≤
      (4 : ℝ) ^ m * ∫ x, |f x| ^ 2

end ReyZygmundVerification
