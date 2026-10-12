import ReyZygmund.MathlibOnly.Proof.BoundaryBridge
import ReyZygmund.MathlibOnly.Proof.GridBridge

/-!
# Routine contracts for the new representation bridges

These helper contracts deliberately name both representations. They are not
the seven independent mathematical specifications, which import only Mathlib
and their own Definitions file. This module is never imported by a solution.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal

namespace ReyZygmundVerification.MathlibOnlyBridges

open ReyZygmund

def midpointChildren : Prop :=
  ∀ {d : ℕ} (D : MathlibOnly.Proof.CubeGrid d) {k : ℤ} {Q R : Box (Fin d)},
    Q ∈ D.cubes k → R ∈ Prepartition.splitCenter Q → R ∈ D.cubes (k - 1)

def independentGridRoundTrip : Prop :=
  ∀ {d : ℕ} (D : MathlibOnly.Proof.CubeGrid d),
    MathlibOnly.Proof.ofDyadicGrid D.toDyadicGrid = D

def implementationGridRoundTrip : Prop :=
  ∀ {d : ℕ} (D : Geometry.DyadicGrid d),
    (MathlibOnly.Proof.ofDyadicGrid D).toDyadicGrid = D

def extendedAverage : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    MathlibOnly.Proof.maximal G f = ReyZygmundVerification.Challenges.endpointMaximal G f

def shiftedCubeFormula : Prop :=
  ∀ {d : ℕ} (tau : Fin d → Fin 3) (k : ℤ),
    MathlibOnly.Proof.shiftedCubes tau k = (Geometry.shiftedDyadicGrid d tau).cubes (-k)

def continuousConvention : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    MathlibOnly.Proof.maximal (MathlibOnly.Proof.continuousRectangles d phi) f =
      Continuous.icoEuclideanFamilyMaximal (MathlibOnly.Proof.continuousRectangles d phi) f

def continuousMeasurability : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    Measurable (MathlibOnly.Proof.maximal (MathlibOnly.Proof.continuousRectangles d phi) f)

def roundedConvention : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ} (tau : ∀ i, Fin (d i) → Fin 3)
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    MathlibOnly.Proof.maximal (MathlibOnly.Proof.roundedRectangles tau phi) f =ᵐ[volume]
      Continuous.icoEuclideanFamilyMaximal (MathlibOnly.Proof.roundedRectangles tau phi) f

end ReyZygmundVerification.MathlibOnlyBridges
