import ReyZygmund.MathlibOnly.Proof.BoundaryBridge
import ReyZygmund.Geometry.Grids
import Verification.Statements.Endpoints

/-!
# Contracts for grid, average and boundary identifications

These helper contracts state the supporting identifications explicitly.
The public mathematical specifications are in `MathlibOnly.Statements`
and `MathlibOnly.SupportingStatements`.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal

namespace ReyZygmundVerification.MathlibOnlyBridges

open ReyZygmund

def midpointChildren : Prop :=
  ∀ {d : ℕ} (D : MathlibOnly.CubeGrid d) {k : ℤ} {Q R : Box (Fin d)},
    Q ∈ D.cubes k → R ∈ Prepartition.splitCenter Q → R ∈ D.cubes (k - 1)

def generationIndex : Prop :=
  ∀ {d : ℕ} (D : MathlibOnly.CubeGrid d) (k : ℤ),
    D.cubesAtGeneration (-k) = D.cubes k

def allGenerations : Prop :=
  ∀ {d : ℕ} (D : MathlibOnly.CubeGrid d) {Q : Box (Fin d)},
    (∃ n : ℤ, Q ∈ D.cubesAtGeneration n) ↔ ∃ k : ℤ, Q ∈ D.cubes k

def extendedAverage : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    MathlibOnly.maximal G f = ReyZygmundVerification.endpointMaximal G f

def shiftedCubeFormula : Prop :=
  ∀ {d : ℕ} (tau : Fin d → Fin 3) (k : ℤ),
    MathlibOnly.shiftedCubes tau k = (Geometry.shiftedDyadicGrid d tau).cubesAtGeneration (-k)

def continuousConvention : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    MathlibOnly.maximal (MathlibOnly.zygmundRectangles d phi) f =
      Continuous.icoEuclideanFamilyMaximal (MathlibOnly.zygmundRectangles d phi) f

def continuousMeasurability : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    Measurable (MathlibOnly.maximal (MathlibOnly.zygmundRectangles d phi) f)

def roundedConvention : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ} (tau : ∀ i, Fin (d i) → Fin 3)
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    MathlibOnly.maximal (MathlibOnly.roundedRectangles tau phi) f =ᵐ[volume]
      Continuous.icoEuclideanFamilyMaximal (MathlibOnly.roundedRectangles tau phi) f

end ReyZygmundVerification.MathlibOnlyBridges
