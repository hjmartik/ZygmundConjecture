import ReyZygmund.Continuous.HalfOpenBoundary
import ReyZygmund.Geometry.PhiRectangles

/-! Explicit propositions for the pointwise all-position half-open bridge. -/

open BoxIntegral MeasureTheory
open ReyZygmund ReyZygmund.Geometry ReyZygmund.Continuous
open scoped BigOperators ENNReal

namespace ReyZygmundVerification

def continuousIcoMaximalEqContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    icoEuclideanFamilyMaximal (continuousPhiRectangles d phi) f =
      euclideanFamilyMaximal (continuousPhiRectangles d phi) f

def continuousIcoMaximalMeasurableContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    Measurable (icoEuclideanFamilyMaximal (continuousPhiRectangles d phi) f)

def continuousIcoMaximalLevelsetContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    ∀ lam : ℝ≥0∞,
      volume {x | lam < icoEuclideanFamilyMaximal (continuousPhiRectangles d phi) f x} =
        volume {x | lam < euclideanFamilyMaximal (continuousPhiRectangles d phi) f x}

end ReyZygmundVerification
