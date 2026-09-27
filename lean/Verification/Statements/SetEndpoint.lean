import ReyZygmund.Maximal.SetFamily
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.MetricSpace.Bounded

/-! Contracts for endpoint interpolation on measurable sets.
No candidate theorem or analytic law is used in these proposition bodies. -/

open MeasureTheory
open scoped ENNReal

namespace ReyZygmundVerification

open ReyZygmund

def setFamilyMaximalMeasurableContract : Prop :=
  ∀ {d : ℕ} (E : Set (Set (Fin d → ℝ))), E.Countable →
    (∀ I ∈ E, MeasurableSet I) → ∀ f : (Fin d → ℝ) → ℝ,
      Measurable (setFamilyMaximal E f)

def setFamilyMaximalInputMonotoneContract : Prop :=
  ∀ {d : ℕ} (E : Set (Set (Fin d → ℝ))) (f g : (Fin d → ℝ) → ℝ),
    (∀ x, |f x| ≤ |g x|) → ∀ x,
      setFamilyMaximal E f x ≤ setFamilyMaximal E g x

def setFamilyMaximalBoundedContract : Prop :=
  ∀ {d : ℕ} (E : Set (Set (Fin d → ℝ))),
    (∀ I ∈ E, 0 < volume I) → (∀ I ∈ E, volume I < ∞) →
    ∀ (f : (Fin d → ℝ) → ℝ) (B : ℝ), 0 ≤ B →
      (∀ x, |f x| ≤ B) → ∀ x, setFamilyMaximal E f x ≤ ENNReal.ofReal B

def setIntegralMeanContract : Prop :=
  ∀ {d : ℕ} (I : Set (Fin d → ℝ)), 0 < volume I → volume I < ∞ →
    ∀ f : (Fin d → ℝ) → ℝ, IntegrableOn f I volume →
      (∫⁻ y in I, ENNReal.ofReal |f y|) / volume I =
        ENNReal.ofReal ((∫ y in I, |f y|) / volume.real I)

def setMaximalTruncationLevelsetContract : Prop :=
  ∀ {d : ℕ} (E : Set (Set (Fin d → ℝ))),
    (∀ I ∈ E, 0 < volume I) → (∀ I ∈ E, volume I < ∞) →
    ∀ f : (Fin d → ℝ) → ℝ, Measurable f → (∀ x, 0 ≤ f x) →
      ∀ lam : ℝ, 0 < lam →
        {x | ENNReal.ofReal lam < setFamilyMaximal E f x} ⊆
          {x | ENNReal.ofReal (lam / 2) < setFamilyMaximal E
            ({y | lam / 2 < f y}.indicator f) x}

def finiteSetEndpointBoundedPowerContract : Prop :=
  ∀ {d : ℕ} (H : Finset (Set (Fin d → ℝ))),
    (∀ I ∈ H, MeasurableSet I) → (∀ I ∈ H, 0 < volume I) →
    (∀ I ∈ H, volume I < ∞) → ∀ (k : ℕ) (A : ℝ), 0 ≤ A →
    (∀ h : (Fin d → ℝ) → ℝ,
      Measurable h → (∀ x, 0 ≤ h x) → (∃ B : ℝ, ∀ x, h x ≤ B) →
      Bornology.IsBounded (Function.support h) → ∀ t : ℝ, 0 < t →
        volume {x | ENNReal.ofReal t < setFamilyMaximal (H : Set _) h x} ≤
          ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
            (|h x| / t * (Real.log (Real.exp 1 + |h x| / t)) ^ k)) →
    ∀ f : (Fin d → ℝ) → ℝ, Measurable f → (∀ x, 0 ≤ f x) →
      (∃ B : ℝ, ∀ x, f x ≤ B) → Bornology.IsBounded (Function.support f) →
      ∀ p : ℝ, 1 < p → p ≤ 2 →
        (∫⁻ x, (setFamilyMaximal (H : Set _) f x) ^ p) ≤
          ENNReal.ofReal (8 * A * Real.exp 2 * (k.factorial : ℝ) /
            (p - 1) ^ (k + 1)) * ∫⁻ x, (ENNReal.ofReal |f x|) ^ p

def finiteSetEndpointPowerContract : Prop :=
  ∀ {d : ℕ} (H : Finset (Set (Fin d → ℝ))),
    (∀ I ∈ H, MeasurableSet I) → (∀ I ∈ H, 0 < volume I) →
    (∀ I ∈ H, volume I < ∞) → ∀ (k : ℕ) (A : ℝ), 1 ≤ A →
    (∀ h : (Fin d → ℝ) → ℝ,
      Measurable h → (∀ x, 0 ≤ h x) → (∃ B : ℝ, ∀ x, h x ≤ B) →
      Bornology.IsBounded (Function.support h) → ∀ t : ℝ, 0 < t →
        volume {x | ENNReal.ofReal t < setFamilyMaximal (H : Set _) h x} ≤
          ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
            (|h x| / t * (Real.log (Real.exp 1 + |h x| / t)) ^ k)) →
    ∀ f : (Fin d → ℝ) → ℝ, Measurable f → ∀ p : ℝ, 1 < p → p ≤ 2 →
      (∫⁻ x, (setFamilyMaximal (H : Set _) f x) ^ p) ≤
        ENNReal.ofReal (8 * A * Real.exp 2 * (k.factorial : ℝ) /
          (p - 1) ^ (k + 1)) * ∫⁻ x, (ENNReal.ofReal |f x|) ^ p

end ReyZygmundVerification
