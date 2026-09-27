import ReyZygmund.Overlap.Finite
import ReyZygmund.Maximal.FiniteIdentification

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry ReyZygmund.Overlap

def finiteFamilyIdentificationContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i))))
    (f : ProductPoint d → ℝ) (x : ProductPoint d),
    familyMaximal (G : Set _) f x = ENNReal.ofReal (finiteFunctionMaximal G f x)

def finiteEuclideanMaximalFiniteContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (x : Fin (∑ i, d i) → ℝ),
    euclideanFamilyMaximal (G : Set _) f x < ∞

def finiteEuclideanMaximalIntegrableContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ),
    Integrable (fun x => (euclideanFamilyMaximal (G : Set _) f x).toReal) volume

def finiteShadowMeasureContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i)))),
    volume (finiteShadow G) < ∞

def finiteOverlapMemLpContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i)))) (p : ℝ≥0∞),
    MemLp (finiteOverlap G) p volume

def finiteOverlapPowerIntegrableContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i))))
    (q : ℝ), 0 < q → Integrable (fun x => Real.rpow (finiteOverlap G x) q) volume

end ReyZygmundVerification
