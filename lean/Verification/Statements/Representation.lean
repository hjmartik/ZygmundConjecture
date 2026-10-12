import ReyZygmund.MathlibOnly.Definitions
import ReyZygmund.MathlibOnly.Proof.EstimateDefinitions

/-!
# Contracts for the representations used by the public proofs

These explicit statements check the maximal, exponential and finite-sum
identifications. The six public theorem contracts are the independent statements
in `ReyZygmund.MathlibOnly.Statements`; their proofs also use the generic norm
and integral identifications.
-/

open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmundVerification.Representation

open ReyZygmund.MathlibOnly

def maximal : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Set (Rectangle d)) (f : Point d → ℝ),
    ReyZygmund.MathlibOnly.maximal G f = Proof.maximal G f

def maximalIco : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Set (Rectangle d)) (f : Point d → ℝ),
    ReyZygmund.MathlibOnly.maximalIco G f = Proof.Estimates.maximalIco G f

def exponential : Prop :=
  ∀ {t : ℝ}, 0 ≤ t → exp (ENNReal.ofReal t) = ENNReal.ofReal (Real.exp t)

def exponentialPower : Prop :=
  ∀ {t : ℝ≥0∞}, t < ∞ → ∀ {c a beta : ℝ}, 0 ≤ c → 0 ≤ a → 0 ≤ beta →
    exp (ENNReal.ofReal c * (ENNReal.ofReal a * t) ^ beta) =
      ENNReal.ofReal (Real.exp (c * Real.rpow (a * t.toReal) beta))

def finiteOverlap : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Finset (Rectangle d)) (x : Point d),
    (overlap (G : Set (Rectangle d)) x).toReal =
      ∑ R ∈ G, (rectangle R).indicator (fun _ => (1 : ℝ)) x

end ReyZygmundVerification.Representation
