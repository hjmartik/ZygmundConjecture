import ReyZygmund.Continuous.HalfOpenBoundary

/-! Explicit propositions for the countable half-open convention bridge. -/

open BoxIntegral MeasureTheory
open ReyZygmund ReyZygmund.Geometry ReyZygmund.Continuous
open scoped BigOperators Classical ENNReal

namespace ReyZygmundVerification

def icoRectangleAeContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (Q : ∀ i, Box (Fin (d i))),
    icoFlatProductBox Q =ᵐ[volume]
      (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ))

def icoRectangleVolumeContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (Q : ∀ i, Box (Fin (d i))),
    volume (icoFlatProductBox Q) =
      volume (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ))

def icoRectanglePositiveFiniteContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (Q : ∀ i, Box (Fin (d i))),
    0 < volume.real (icoFlatProductBox Q) ∧ volume (icoFlatProductBox Q) < ∞

def icoRectangleIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (Q : ∀ i, Box (Fin (d i)))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ),
    (∫ x in icoFlatProductBox Q, f x) =
      ∫ x in (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)), f x

def icoRectangleLocalIntegrabilityContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (Q : ∀ i, Box (Fin (d i)))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    IntegrableOn f (icoFlatProductBox Q) volume

def icoMaximalAeContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i)))), G.Countable →
    ∀ f : (Fin (∑ i, d i) → ℝ) → ℝ,
      icoEuclideanFamilyMaximal G f =ᵐ[volume] euclideanFamilyMaximal G f

def icoMaximalLevelsetContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i)))), G.Countable →
    ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ) (lam : ℝ), 0 < lam →
      volume {x | ENNReal.ofReal lam < icoEuclideanFamilyMaximal G f x} =
        volume {x | ENNReal.ofReal lam < euclideanFamilyMaximal G f x}

end ReyZygmundVerification
