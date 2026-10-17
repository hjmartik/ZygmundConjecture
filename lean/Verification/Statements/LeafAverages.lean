import ReyZygmund.Geometry.LeafAverages

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmundVerification

open ReyZygmund.Geometry ReyZygmund.Projection

def leafAverageValueContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i)))
    (N : Fin m → ℕ) (f : ProductPoint d → ℝ)
    (Q : ∀ i, Box (Fin (d i))), Q ∈ productLeaves I N →
  ∀ (x : ProductPoint d), x ∈ productRectangle Q →
    leafAverage I N f x = (∫ y in productRectangle Q, f y) / volume.real (productRectangle Q)

def leafAverageIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i)))
    (N : Fin m → ℕ) (R : ∀ i, Box (Fin (d i))), R ∈ productDescendants I N →
  ∀ (f : ProductPoint d → ℝ), IntegrableOn f (productRectangle I) volume →
    (∫ x in productRectangle R, leafAverage I N f x) = ∫ x in productRectangle R, f x

def leafAveragePowerContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i)))
    (N : Fin m → ℕ) (f : ProductPoint d → ℝ) (p : ℝ), 1 ≤ p →
  IntegrableOn f (productRectangle I) volume →
  IntegrableOn (fun x => Real.rpow |f x| p) (productRectangle I) volume →
    (∫ x in productRectangle I, Real.rpow |leafAverage I N f x| p) ≤
      ∫ x in productRectangle I, Real.rpow |f x| p

end ReyZygmundVerification
