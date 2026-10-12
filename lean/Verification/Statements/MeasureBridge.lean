import ReyZygmund.MathlibOnly.Proof.EstimateDefinitions
import ReyZygmund.Continuous.HalfOpenBoundary
import ReyZygmund.Overlap.Countable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Explicit contracts for measurability and integral identifications

These supporting contracts state the measurability and integral identities directly.
They use implementation definitions where an identification requires them;
the six independent public specifications remain in MathlibOnly.Proof.
-/

open BoxIntegral MeasureTheory Filter ReyZygmund
open ReyZygmund.MathlibOnly.Proof ReyZygmund.MathlibOnly.Proof.Estimates
open scoped BigOperators ENNReal Classical Topology

namespace ReyZygmundVerification.MeasureBridge

noncomputable section

def sparse_iff_borelContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (eta : ℝ) (G : Set (∀ i, Box (Fin (d i)))),
    MathlibOnly.Proof.Estimates.Sparse eta G ↔ MathlibOnly.Proof.Sparse eta G

def rectangleIco_eqContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (R : ∀ i, Box (Fin (d i))),
    rectangleIco R = Continuous.icoFlatProductBox R

def maximalIco_eqContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
      maximalIco G f = Continuous.icoEuclideanFamilyMaximal G f

def rounded_levelset_measure_eqContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ} (tau : ∀ i, Fin (d i) → Fin 3)
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume → ∀ lam : ℝ,
      volume {x | ENNReal.ofReal lam < maximalIco (roundedRectangles tau phi) f x} =
        volume {x | ENNReal.ofReal lam < maximal (roundedRectangles tau phi) f x}

def shadow_eqContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i)))),
    shadow G = Overlap.shadow G

def overlap_eqContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i)))),
    overlap G = Overlap.overlap G

def integrableOn_overlap_exponentialContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (H : Finset (∀ i, Box (Fin (d i))))
    (c beta : ℝ), 0 < c → 0 < beta →
      IntegrableOn (fun x => Real.exp (c * Real.rpow
        (overlap (H : Set (∀ i, Box (Fin (d i)))) x).toReal beta))
        (shadow (H : Set (∀ i, Box (Fin (d i))))) volume

def lintegral_overlap_exponential_eqContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (H : Finset (∀ i, Box (Fin (d i))))
    (c beta : ℝ), 0 < c → 0 < beta →
      (∫⁻ x in shadow (H : Set (∀ i, Box (Fin (d i)))), ENNReal.ofReal
        (Real.exp (c * Real.rpow (overlap (H : Set (∀ i, Box (Fin (d i)))) x).toReal beta))) =
      ENNReal.ofReal (∫ x in shadow (H : Set (∀ i, Box (Fin (d i)))),
        Real.exp (c * Real.rpow (overlap (H : Set (∀ i, Box (Fin (d i)))) x).toReal beta))

def tendsto_overlap_exponential_iffContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : ℕ → Finset (∀ i, Box (Fin (d i))))
    (c beta : ℝ), 0 < c → 0 < beta →
      (Tendsto (fun N => ∫⁻ x in shadow (G N : Set (∀ i, Box (Fin (d i)))), ENNReal.ofReal
        (Real.exp (c * Real.rpow (overlap (G N : Set (∀ i, Box (Fin (d i)))) x).toReal beta)))
        atTop (𝓝 ∞) ↔
      Tendsto (fun N => ∫ x in shadow (G N : Set (∀ i, Box (Fin (d i)))),
        Real.exp (c * Real.rpow (overlap (G N : Set (∀ i, Box (Fin (d i)))) x).toReal beta))
        atTop atTop)

end
end ReyZygmundVerification.MeasureBridge
