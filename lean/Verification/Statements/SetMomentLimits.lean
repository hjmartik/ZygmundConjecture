import ReyZygmund.Overlap.SetDefinitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Independent explicit contracts for the countable set-overlap moment limits.
Only the shadow/overlap definitions and Mathlib are imported. The
natural exponent is the moment-growth order, not the endpoint logarithmic
order. These statements do not import any candidate moment proof. -/

open MeasureTheory
open scoped ENNReal
open ReyZygmund.Overlap

namespace ReyZygmundVerification

def setOverlapAeFiniteFromHighMomentsContract : Prop :=
  ∀ {d : ℕ} (G : Set (Set (Fin d → ℝ))), G.Countable →
    (∀ I ∈ G, MeasurableSet I) → volume (setShadow G) < ∞ →
    ∀ (k : ℕ) (C : ℝ),
      (∀ q : ℝ, 2 ≤ q →
        (∫⁻ x, (setOverlap G x) ^ q) ≤
          (ENNReal.ofReal (C * (q - 1) ^ k)) ^ q * volume (setShadow G)) →
      ∀ᵐ x ∂volume, setOverlap G x < ∞

def setOverlapShadowAllMomentsContract : Prop :=
  ∀ {d : ℕ} (G : Set (Set (Fin d → ℝ))), G.Countable →
    (∀ I ∈ G, MeasurableSet I) → volume (setShadow G) < ∞ →
    ∀ (k : ℕ) (C : ℝ), 0 ≤ C →
      (∀ q : ℝ, 2 ≤ q →
        (∫⁻ x, (setOverlap G x) ^ q) ≤
          (ENNReal.ofReal (C * (q - 1) ^ k)) ^ q * volume (setShadow G)) →
      ∀ q : ℝ, 1 ≤ q →
        (∫⁻ x in setShadow G, (ENNReal.ofReal (setOverlap G x).toReal) ^ q) ≤
          (ENNReal.ofReal (C * q ^ k)) ^ q * volume (setShadow G)

def setOverlapAllMomentsContract : Prop :=
  ∀ {d : ℕ} (G : Set (Set (Fin d → ℝ))), G.Countable →
    (∀ I ∈ G, MeasurableSet I) → volume (setShadow G) < ∞ →
    ∀ (k : ℕ) (C : ℝ), 0 ≤ C →
      (∀ q : ℝ, 2 ≤ q →
        (∫⁻ x, (setOverlap G x) ^ q) ≤
          (ENNReal.ofReal (C * (q - 1) ^ k)) ^ q * volume (setShadow G)) →
      ∀ q : ℝ, 1 ≤ q →
        (∫⁻ x, (setOverlap G x) ^ q) ≤
          (ENNReal.ofReal (C * q ^ k)) ^ q * volume (setShadow G)

def setOverlapNormFromHighMomentsContract : Prop :=
  ∀ {d : ℕ} (G : Set (Set (Fin d → ℝ))), G.Countable →
    (∀ I ∈ G, MeasurableSet I) → volume (setShadow G) < ∞ →
    ∀ (k : ℕ) (C : ℝ), 0 ≤ C →
      (∀ q : ℝ, 2 ≤ q →
        (∫⁻ x, (setOverlap G x) ^ q) ≤
          (ENNReal.ofReal (C * (q - 1) ^ k)) ^ q * volume (setShadow G)) →
      ∀ q : ℝ, 1 ≤ q →
        eLpNorm (fun x => (setOverlap G x).toReal) (ENNReal.ofReal q) volume ≤
          ENNReal.ofReal (C * q ^ k) * (volume (setShadow G)) ^ (1 / q)

def setOverlapExponentialFromHighMomentsContract : Prop :=
  ∀ {d : ℕ} (G : Set (Set (Fin d → ℝ))), G.Countable →
    (∀ I ∈ G, MeasurableSet I) → volume (setShadow G) < ∞ →
    ∀ k : ℕ, 1 ≤ k → ∀ C : ℝ, 0 < C →
      (∀ q : ℝ, 2 ≤ q →
        (∫⁻ x, (setOverlap G x) ^ q) ≤
          (ENNReal.ofReal (C * (q - 1) ^ k)) ^ q * volume (setShadow G)) →
      (∀ᵐ x ∂volume, setOverlap G x < ∞) ∧
        (∫⁻ x in setShadow G, ENNReal.ofReal (Real.exp
          ((1 / 2 : ℝ) * Real.rpow ((setOverlap G x).toReal / (Real.exp 1 * C))
            (1 / (k : ℝ))))) ≤ 3 * volume (setShadow G)

end ReyZygmundVerification
