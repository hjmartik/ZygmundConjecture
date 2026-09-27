import ReyZygmund.Geometry.ProductJensen

/-! Jensen's inequality on the top rectangle, without a finite step-function hypothesis. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmundVerification

open ReyZygmund.Geometry

def productBoxVolumePositiveContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))),
    0 < volume.real (productBox I)

def productBoxVolumeFiniteContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))),
    volume (productBox I) < ⊤

def productBoxAverageJensenContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i)))
    (f : ProductPoint d → ℝ) (p : ℝ), 1 ≤ p →
    IntegrableOn f (productBox I) volume →
    IntegrableOn (fun x => Real.rpow |f x| p) (productBox I) volume →
    Real.rpow |(∫ x in productBox I, f x) / volume.real (productBox I)| p ≤
      (∫ x in productBox I, Real.rpow |f x| p) / volume.real (productBox I)

end ReyZygmundVerification
