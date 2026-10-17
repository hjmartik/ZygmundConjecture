import ReyZygmund.Maximal.OrdinaryGrid

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal

open ReyZygmund.MathlibOnly (CubeGrid gridRectangles)

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry ReyZygmund.Projection

def finiteOrdinaryInputIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ i, 0 < d i) →
    ∀ G : Finset (∀ i, Box (Fin (d i))), G ⊆ productDescendants I N →
    ∀ (f : ProductPoint d → ℝ) (p : ℝ), 1 < p →
    IntegrableOn f (productRectangle I) volume →
    IntegrableOn (fun x => Real.rpow |f x| p) (productRectangle I) volume →
    (∫ x in productRectangle I, Real.rpow (finiteFunctionMaximal G f x) p) ≤
      Real.rpow (p / (p - 1)) (p * (m : ℝ)) *
        ∫ x in productRectangle I, Real.rpow |f x| p

def finiteOrdinaryGridSquareContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, (∀ i, 0 < d i) →
    ∀ (D : ∀ i, CubeGrid (d i)) (G : Finset (∀ i, Box (Fin (d i)))),
    (↑G : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D →
    ∀ f : ProductPoint d → ℝ, MemLp f 2 volume →
    (∫ x, (finiteFunctionMaximal G f x) ^ 2) ≤
      (4 : ℝ) ^ m * ∫ x, |f x| ^ 2

end ReyZygmundVerification
