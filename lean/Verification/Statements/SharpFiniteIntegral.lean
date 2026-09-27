import ReyZygmund.Sharpness.FiniteIntegral

/-! Explicit propositions for the finite sharpness-integral interpretation. -/

open BoxIntegral MeasureTheory Filter ReyZygmund.Overlap
open scoped BigOperators Classical ENNReal Topology

namespace ReyZygmundVerification

def finiteOverlapExponentialNonnegContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (H : Finset (∀ i, Box (Fin (d i)))) (c beta : ℝ), 0 ≤ c →
    ∀ x : Fin (∑ i, d i) → ℝ,
      0 ≤ Real.exp (c * Real.rpow (finiteOverlap H x) beta) - 1

def finiteOverlapExponentialIntegrableContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (H : Finset (∀ i, Box (Fin (d i)))) (c beta : ℝ), 0 < c → 0 < beta →
    IntegrableOn (fun x => Real.exp (c * Real.rpow (finiteOverlap H x) beta) - 1)
      (finiteShadow H) volume

def overlapFinsetExponentialIntegrableContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (H : Finset (∀ i, Box (Fin (d i)))) (c beta : ℝ), 0 < c → 0 < beta →
    IntegrableOn (fun x => Real.exp (c * Real.rpow
      (overlap (H : Set (∀ i, Box (Fin (d i)))) x).toReal beta) - 1)
      (shadow (H : Set (∀ i, Box (Fin (d i))))) volume

def overlapFinsetExponentialIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (H : Finset (∀ i, Box (Fin (d i)))) (c beta : ℝ), 0 < c → 0 < beta →
    (∫⁻ x in shadow (H : Set (∀ i, Box (Fin (d i)))), ENNReal.ofReal
      (Real.exp (c * Real.rpow
        (overlap (H : Set (∀ i, Box (Fin (d i)))) x).toReal beta)) - 1) =
      ENNReal.ofReal (∫ x in finiteShadow H,
        Real.exp (c * Real.rpow (finiteOverlap H x) beta) - 1)

def finiteOverlapExponentialLimitContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (G : ℕ → Finset (∀ i, Box (Fin (d i)))) (c beta : ℝ), 0 < c → 0 < beta →
    (Tendsto (fun N : ℕ =>
      ∫⁻ x in shadow (G N : Set (∀ i, Box (Fin (d i)))), ENNReal.ofReal
        (Real.exp (c * Real.rpow
          (overlap (G N : Set (∀ i, Box (Fin (d i)))) x).toReal beta)) - 1)
      atTop (𝓝 ∞) ↔
    Tendsto (fun N : ℕ => ∫ x in finiteShadow (G N),
      Real.exp (c * Real.rpow (finiteOverlap (G N) x) beta) - 1) atTop atTop)

end ReyZygmundVerification
