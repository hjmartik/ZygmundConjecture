import ReyZygmund.Geometry.ProductJensen

/-! Jensen's inequality on the top rectangle, without a finite step-function hypothesis. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmundVerification

open ReyZygmund.Geometry

def productRectangleVolumePositiveContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))),
    0 < volume.real (productRectangle I)

def productRectangleVolumeFiniteContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))),
    volume (productRectangle I) < ⊤

def productRectangleAverageJensenContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i)))
    (f : ProductPoint d → ℝ) (p : ℝ), 1 ≤ p →
    IntegrableOn f (productRectangle I) volume →
    IntegrableOn (fun x => Real.rpow |f x| p) (productRectangle I) volume →
    Real.rpow |(∫ x in productRectangle I, f x) / volume.real (productRectangle I)| p ≤
      (∫ x in productRectangle I, Real.rpow |f x| p) / volume.real (productRectangle I)

end ReyZygmundVerification
