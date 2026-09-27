import ReyZygmund.Maximal.SetFamily
import ReyZygmund.Overlap.SetDefinitions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-! Statements of the endpoint-to-overlap implication. The project imports provide
only maximal, shadow and extended overlap definitions. The endpoint, pairing and
moment proofs are not imported. Here `k` is the endpoint logarithmic order.
-/

open MeasureTheory
open scoped ENNReal
open ReyZygmund ReyZygmund.Overlap

namespace ReyZygmundVerification

def setEndpointSparseOverlapBoundedTestsContract : Prop :=
  ∀ {d : ℕ} (E : Set (Set (Fin d → ℝ))), E.Countable →
    (∀ I ∈ E, MeasurableSet I) → (∀ I ∈ E, 0 < volume I) →
    (∀ I ∈ E, volume I < ∞) → ∀ (k : ℕ) (A : ℝ), 1 ≤ A →
    (∀ f : (Fin d → ℝ) → ℝ,
      Measurable f → (∀ x, 0 ≤ f x) → (∃ B : ℝ, ∀ x, f x ≤ B) →
      Bornology.IsBounded (Function.support f) → ∀ t : ℝ, 0 < t →
        volume {x | ENNReal.ofReal t < setFamilyMaximal E f x} ≤
          ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
            (|f x| / t * (Real.log (Real.exp 1 + |f x| / t)) ^ k)) →
    ∀ G : Set (Set (Fin d → ℝ)), G ⊆ E →
    ∀ eta : ℝ, 0 < eta → eta ≤ 1 →
    ∀ W : Set (Fin d → ℝ) → Set (Fin d → ℝ),
      (∀ I ∈ G, MeasurableSet (W I)) → (∀ I ∈ G, W I ⊆ I) →
      Set.Pairwise G (fun I J => Disjoint (W I) (W J)) →
      (∀ I ∈ G, ENNReal.ofReal eta * volume I ≤ volume (W I)) →
      volume (setShadow G) < ∞ →
      let D := 8 * A * Real.exp 2 * (k.factorial : ℝ)
      (∀ᵐ x ∂volume, setOverlap G x < ∞) ∧
        (∀ q : ℝ, 1 ≤ q →
          eLpNorm (fun x => (setOverlap G x).toReal) (ENNReal.ofReal q) volume ≤
            ENNReal.ofReal ((D / eta) * q ^ (k + 1)) *
              (volume (setShadow G)) ^ (1 / q)) ∧
        (∫⁻ x in setShadow G, ENNReal.ofReal (Real.exp
          ((1 / 2 : ℝ) * Real.rpow
            (eta * (setOverlap G x).toReal / (Real.exp 1 * D))
            (1 / ((k + 1 : ℕ) : ℝ))))) ≤ 3 * volume (setShadow G)

def setEndpointSparseOverlapContract : Prop :=
  ∀ {d : ℕ} (E : Set (Set (Fin d → ℝ))), E.Countable →
    (∀ I ∈ E, MeasurableSet I) → (∀ I ∈ E, 0 < volume I) →
    (∀ I ∈ E, volume I < ∞) → ∀ (k : ℕ) (A : ℝ), 1 ≤ A →
    (∀ f : (Fin d → ℝ) → ℝ, Measurable f → ∀ t : ℝ, 0 < t →
      volume {x | ENNReal.ofReal t < setFamilyMaximal E f x} ≤
        ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
          (|f x| / t * (Real.log (Real.exp 1 + |f x| / t)) ^ k)) →
    ∀ G : Set (Set (Fin d → ℝ)), G ⊆ E →
    ∀ eta : ℝ, 0 < eta → eta ≤ 1 →
    ∀ W : Set (Fin d → ℝ) → Set (Fin d → ℝ),
      (∀ I ∈ G, MeasurableSet (W I)) → (∀ I ∈ G, W I ⊆ I) →
      Set.Pairwise G (fun I J => Disjoint (W I) (W J)) →
      (∀ I ∈ G, ENNReal.ofReal eta * volume I ≤ volume (W I)) →
      volume (setShadow G) < ∞ →
      let D := 8 * A * Real.exp 2 * (k.factorial : ℝ)
      (∀ᵐ x ∂volume, setOverlap G x < ∞) ∧
        (∀ q : ℝ, 1 ≤ q →
          eLpNorm (fun x => (setOverlap G x).toReal) (ENNReal.ofReal q) volume ≤
            ENNReal.ofReal ((D / eta) * q ^ (k + 1)) *
              (volume (setShadow G)) ^ (1 / q)) ∧
        (∫⁻ x in setShadow G, ENNReal.ofReal (Real.exp
          ((1 / 2 : ℝ) * Real.rpow
            (eta * (setOverlap G x).toReal / (Real.exp 1 * D))
            (1 / ((k + 1 : ℕ) : ℝ))))) ≤ 3 * volume (setShadow G)

end ReyZygmundVerification
