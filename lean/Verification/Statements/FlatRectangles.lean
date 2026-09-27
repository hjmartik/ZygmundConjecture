import ReyZygmund.Geometry.FlatRectangles

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal

namespace ReyZygmundVerification

open ReyZygmund.Geometry

def flatProductBoxMembershipContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (Q : ∀ i, Box (Fin (d i))) (x : ProductPoint d),
    flattenCoordinates d x ∈ flatProductBox Q ↔ x ∈ productBox Q

def flatProductBoxPreimageContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (Q : ∀ i, Box (Fin (d i))),
    flattenCoordinates d ⁻¹' (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) = productBox Q

def flatProductBoxVolumeContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (Q : ∀ i, Box (Fin (d i))),
    volume (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) = volume (productBox Q)

def flatProductBoxIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (Q : ∀ i, Box (Fin (d i)))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ),
    (∫ x in productBox Q, f (flattenCoordinates d x)) =
      ∫ y in (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)), f y

def flatProductBoxAverageContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (Q : ∀ i, Box (Fin (d i)))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ),
    (∫ x in productBox Q, f (flattenCoordinates d x)) / volume.real (productBox Q) =
      (∫ y in (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)), f y) /
        volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ))

def flattenMemLpContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ≥0∞),
    MemLp f p volume → MemLp (fun x => f (flattenCoordinates d x)) p volume

def flattenELpNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ≥0∞),
    AEStronglyMeasurable f volume →
    eLpNorm (fun x => f (flattenCoordinates d x)) p volume = eLpNorm f p volume

end ReyZygmundVerification
