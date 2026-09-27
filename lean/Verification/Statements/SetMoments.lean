import ReyZygmund.Maximal.SetFamily
import ReyZygmund.Overlap.SetDefinitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! Contracts for finite measurable-set sparse duality. The candidate
proof modules are not imported and no candidate theorem type is aliased. -/

open MeasureTheory
open scoped ENNReal

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Overlap

def finiteSetMaximalFiniteContract : Prop :=
  ∀ {d : ℕ} (H : Finset (Set (Fin d → ℝ))),
    (∀ I ∈ H, 0 < volume I) → (∀ I ∈ H, volume I < ∞) →
    ∀ f : (Fin d → ℝ) → ℝ, (∀ I ∈ H, IntegrableOn f I volume) →
      ∀ x, setFamilyMaximal (H : Set _) f x < ∞

def finiteSetMaximalMemLpContract : Prop :=
  ∀ {d : ℕ} (H : Finset (Set (Fin d → ℝ))),
    (∀ I ∈ H, MeasurableSet I) → (∀ I ∈ H, 0 < volume I) →
    (∀ I ∈ H, volume I < ∞) → ∀ f : (Fin d → ℝ) → ℝ,
      (∀ I ∈ H, IntegrableOn f I volume) → ∀ p : ℝ≥0∞,
        MemLp (fun x => (setFamilyMaximal (H : Set _) f x).toReal) p volume

def finiteSetSparsePairingContract : Prop :=
  ∀ {d : ℕ} (H : Finset (Set (Fin d → ℝ))),
    (∀ I ∈ H, MeasurableSet I) → (∀ I ∈ H, 0 < volume I) →
    (∀ I ∈ H, volume I < ∞) → ∀ eta : ℝ, 0 < eta →
    ∀ E : Set (Fin d → ℝ) → Set (Fin d → ℝ),
      (∀ I ∈ H, MeasurableSet (E I)) → (∀ I ∈ H, E I ⊆ I) →
      Set.Pairwise (H : Set (Set (Fin d → ℝ))) (fun I J => Disjoint (E I) (E J)) →
      (∀ I ∈ H, ENNReal.ofReal eta * volume I ≤ volume (E I)) →
      ∀ g : (Fin d → ℝ) → ℝ,
        (∀ x ∈ finiteSetShadow H, 0 ≤ g x) →
        (∀ I ∈ H, IntegrableOn g I volume) →
          eta * (∫ x, finiteSetOverlap H x * g x) ≤
            ∫ x in finiteSetShadow H, (setFamilyMaximal (H : Set _) g x).toReal

def finiteSetSparseMomentContract : Prop :=
  ∀ {d : ℕ} (H : Finset (Set (Fin d → ℝ))),
    (∀ I ∈ H, MeasurableSet I) → (∀ I ∈ H, 0 < volume I) →
    (∀ I ∈ H, volume I < ∞) → ∀ eta : ℝ, 0 < eta →
    ∀ E : Set (Fin d → ℝ) → Set (Fin d → ℝ),
      (∀ I ∈ H, MeasurableSet (E I)) → (∀ I ∈ H, E I ⊆ I) →
      Set.Pairwise (H : Set (Set (Fin d → ℝ))) (fun I J => Disjoint (E I) (E J)) →
      (∀ I ∈ H, ENNReal.ofReal eta * volume I ≤ volume (E I)) →
      ∀ (k : ℕ) (C : ℝ), 0 < C →
        (∀ f : (Fin d → ℝ) → ℝ, Measurable f → (∀ x, 0 ≤ f x) →
          ∀ p : ℝ, 1 < p → p ≤ 2 →
            (∫⁻ x, (setFamilyMaximal (H : Set _) f x) ^ p) ≤
              (ENNReal.ofReal (C / (p - 1) ^ k)) ^ p *
                ∫⁻ x, (ENNReal.ofReal |f x|) ^ p) →
        ∀ q : ℝ, 2 ≤ q →
          Real.rpow (∫ x, Real.rpow (finiteSetOverlap H x) q) (1 / q) ≤
            C * eta⁻¹ * (q - 1) ^ k *
              Real.rpow (volume.real (finiteSetShadow H)) (1 / q)

def finiteSetSparseMomentLIntegralContract : Prop :=
  ∀ {d : ℕ} (H : Finset (Set (Fin d → ℝ))),
    (∀ I ∈ H, MeasurableSet I) → (∀ I ∈ H, 0 < volume I) →
    (∀ I ∈ H, volume I < ∞) → ∀ eta : ℝ, 0 < eta →
    ∀ E : Set (Fin d → ℝ) → Set (Fin d → ℝ),
      (∀ I ∈ H, MeasurableSet (E I)) → (∀ I ∈ H, E I ⊆ I) →
      Set.Pairwise (H : Set (Set (Fin d → ℝ))) (fun I J => Disjoint (E I) (E J)) →
      (∀ I ∈ H, ENNReal.ofReal eta * volume I ≤ volume (E I)) →
      ∀ (k : ℕ) (C : ℝ), 0 < C →
        (∀ f : (Fin d → ℝ) → ℝ, Measurable f → (∀ x, 0 ≤ f x) →
          ∀ p : ℝ, 1 < p → p ≤ 2 →
            (∫⁻ x, (setFamilyMaximal (H : Set _) f x) ^ p) ≤
              (ENNReal.ofReal (C / (p - 1) ^ k)) ^ p *
                ∫⁻ x, (ENNReal.ofReal |f x|) ^ p) →
        ∀ q : ℝ, 2 ≤ q →
          (∫⁻ x, (ENNReal.ofReal (finiteSetOverlap H x)) ^ q) ≤
            (ENNReal.ofReal (C * eta⁻¹ * (q - 1) ^ k)) ^ q *
              volume (finiteSetShadow H)

end ReyZygmundVerification
