import ReyZygmund.Overlap.SetDefinitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # Independent contracts for measurable-set overlap limits

These explicit propositions use only the finite/countable set-overlap
definitions and Mathlib. No candidate small-moment, finite-overlap or
countable-passage proof module is imported.
-/

open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmundVerification

open ReyZygmund.Overlap

def smallMomentFromSecondContract : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (H : X → ℝ), Measurable H → (∀ x, 0 ≤ H x) → ∀ C : ℝ,
      (∫⁻ x, (ENNReal.ofReal (H x)) ^ (2 : ℝ) ∂μ) ≤
        (ENNReal.ofReal C) ^ (2 : ℝ) * μ Set.univ →
      ∀ q : ℝ, 0 < q → q ≤ 2 →
        (∫⁻ x, (ENNReal.ofReal (H x)) ^ q ∂μ) ≤
          (ENNReal.ofReal C) ^ q * μ Set.univ

def finiteSetSubsetShadowContract : Prop :=
  ∀ {d : ℕ} (H : Finset (Set (Fin d → ℝ))) (I : Set (Fin d → ℝ)),
    I ∈ H → I ⊆ finiteSetShadow H

def finiteSetShadowMeasurableContract : Prop :=
  ∀ {d : ℕ} (H : Finset (Set (Fin d → ℝ))),
    (∀ I ∈ H, MeasurableSet I) → MeasurableSet (finiteSetShadow H)

def finiteSetShadowFiniteVolumeContract : Prop :=
  ∀ {d : ℕ} (H : Finset (Set (Fin d → ℝ))),
    (∀ I ∈ H, volume I < ∞) → volume (finiteSetShadow H) < ∞

def finiteSetOverlapMeasurableContract : Prop :=
  ∀ {d : ℕ} (H : Finset (Set (Fin d → ℝ))),
    (∀ I ∈ H, MeasurableSet I) → Measurable (finiteSetOverlap H)

def finiteSetOverlapNonnegativeContract : Prop :=
  ∀ {d : ℕ} (H : Finset (Set (Fin d → ℝ))) (x : Fin d → ℝ),
    0 ≤ finiteSetOverlap H x

def finiteSetOverlapCardBoundContract : Prop :=
  ∀ {d : ℕ} (H : Finset (Set (Fin d → ℝ))) (x : Fin d → ℝ),
    finiteSetOverlap H x ≤ (H.card : ℝ)

def finiteSetOverlapZeroOutsideContract : Prop :=
  ∀ {d : ℕ} (H : Finset (Set (Fin d → ℝ))) (x : Fin d → ℝ),
    x ∉ finiteSetShadow H → finiteSetOverlap H x = 0

def finiteSetOverlapMemLpContract : Prop :=
  ∀ {d : ℕ} (H : Finset (Set (Fin d → ℝ))),
    (∀ I ∈ H, MeasurableSet I) → (∀ I ∈ H, volume I < ∞) →
      ∀ p : ℝ≥0∞, MemLp (finiteSetOverlap H) p volume

def finiteSetOverlapPowerIntegrableContract : Prop :=
  ∀ {d : ℕ} (H : Finset (Set (Fin d → ℝ))),
    (∀ I ∈ H, MeasurableSet I) → (∀ I ∈ H, volume I < ∞) →
      ∀ q : ℝ, 0 < q →
        Integrable (fun x => Real.rpow (finiteSetOverlap H x) q) volume

def setShadowMeasurableContract : Prop :=
  ∀ {d : ℕ} (G : Set (Set (Fin d → ℝ))), G.Countable →
    (∀ I ∈ G, MeasurableSet I) → MeasurableSet (setShadow G)

def finiteSetShadowSubsetShadowContract : Prop :=
  ∀ {d : ℕ} (G : Set (Set (Fin d → ℝ))) (H : Finset G),
    finiteSetShadow (H.image Subtype.val) ⊆ setShadow G

def setOverlapFiniteSupremumContract : Prop :=
  ∀ {d : ℕ} (G : Set (Set (Fin d → ℝ))) (x : Fin d → ℝ),
    setOverlap G x = ⨆ H : Finset G,
      ENNReal.ofReal (finiteSetOverlap (H.image Subtype.val) x)

def setOverlapMeasurableContract : Prop :=
  ∀ {d : ℕ} (G : Set (Set (Fin d → ℝ))), G.Countable →
    (∀ I ∈ G, MeasurableSet I) → Measurable (setOverlap G)

def setOverlapZeroOutsideContract : Prop :=
  ∀ {d : ℕ} (G : Set (Set (Fin d → ℝ))) (x : Fin d → ℝ),
    x ∉ setShadow G → setOverlap G x = 0

def setOverlapPowerFiniteSupremumContract : Prop :=
  ∀ {d : ℕ} (G : Set (Set (Fin d → ℝ))), G.Countable →
    (∀ I ∈ G, MeasurableSet I) → ∀ q : ℝ, 0 < q →
      (∫⁻ x, (setOverlap G x) ^ q) =
        ⨆ H : Finset G, ∫⁻ x,
          (ENNReal.ofReal (finiteSetOverlap (H.image Subtype.val) x)) ^ q

def countableSetMomentFromFiniteContract : Prop :=
  ∀ {d : ℕ} (G : Set (Set (Fin d → ℝ))), G.Countable →
    (∀ I ∈ G, MeasurableSet I) → ∀ q : ℝ, 0 < q → ∀ C : ℝ≥0∞,
      (∀ H : Finset G,
        (∫⁻ x, (ENNReal.ofReal (finiteSetOverlap (H.image Subtype.val) x)) ^ q) ≤
          C * volume (finiteSetShadow (H.image Subtype.val))) →
      (∫⁻ x, (setOverlap G x) ^ q) ≤ C * volume (setShadow G)

end ReyZygmundVerification
