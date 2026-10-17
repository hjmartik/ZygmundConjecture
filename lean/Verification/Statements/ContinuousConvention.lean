import ReyZygmund.Continuous.HalfOpenBoundary
import ReyZygmund.Geometry.FlatRectangles

/-! Explicit propositions for the pointwise all-position half-open bridge. -/

open BoxIntegral MeasureTheory
open ReyZygmund ReyZygmund.Geometry ReyZygmund.Continuous
open scoped BigOperators ENNReal

open ReyZygmund.MathlibOnly (zygmundRectangles)

namespace ReyZygmundVerification

def continuousIcoMaximalEqContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    icoEuclideanFamilyMaximal (zygmundRectangles d phi) f =
      euclideanFamilyMaximal (zygmundRectangles d phi) f

def continuousIcoMaximalMeasurableContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    Measurable (icoEuclideanFamilyMaximal (zygmundRectangles d phi) f)

def continuousIcoMaximalLevelsetContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    ∀ lam : ℝ≥0∞,
      volume {x | lam < icoEuclideanFamilyMaximal (zygmundRectangles d phi) f x} =
        volume {x | lam < euclideanFamilyMaximal (zygmundRectangles d phi) f x}

end ReyZygmundVerification
