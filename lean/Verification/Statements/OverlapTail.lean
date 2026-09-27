import ReyZygmund.Overlap.Countable
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Explicit expected propositions for the real-moment tail, layer-cake
integration, and the conditional countable-overlap passage. These definitions
do not import or refer to the candidate tail theorems.
-/

open BoxIntegral MeasureTheory ReyZygmund.Geometry ReyZygmund.Overlap
open scoped ENNReal Classical

namespace ReyZygmundVerification

noncomputable def realMomentTailContract : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (mu : Measure X) (H : X → ℝ),
    Measurable H → (∀ x, 0 ≤ H x) →
    ∀ (q M b : ℝ), 0 < q → 0 < M →
    (∫⁻ x, ENNReal.ofReal (Real.rpow (H x) q) ∂mu) ≤
      ENNReal.ofReal (Real.rpow M q) * mu Set.univ →
    mu {x | Real.exp b * M < H x} ≤
      ENNReal.ofReal (Real.exp (-b * q)) * mu Set.univ

noncomputable def polynomialMomentsTailContract : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (mu : Measure X) (H : X → ℝ),
    Measurable H → (∀ x, 0 ≤ H x) → ∀ (k : ℕ) (C : ℝ), 0 < C →
    (∀ q : ℝ, 2 ≤ q →
      (∫⁻ x, ENNReal.ofReal (Real.rpow (H x) q) ∂mu) ≤
        ENNReal.ofReal (Real.rpow (C * q ^ k) q) * mu Set.univ) →
    ∀ u : ℝ, 0 ≤ u →
    mu {x | Real.exp 2 * C * u ^ k < H x} ≤
      ENNReal.ofReal (Real.exp 4 * Real.exp (-2 * u)) * mu Set.univ

noncomputable def exponentialTailIntegralContract : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (Y : X → ℝ), Measurable Y → (∀ x, 0 ≤ Y x) →
    ∀ (C a c : ℝ), 0 ≤ C → 0 < c → c < a →
    (∀ t : ℝ, 0 ≤ t →
      mu {x | t < Y x} ≤ ENNReal.ofReal (C * Real.exp (-a * t)) * mu Set.univ) →
    (∫⁻ x, ENNReal.ofReal (Real.exp (c * Y x) - 1) ∂mu) ≤
      ENNReal.ofReal (C * c / (a - c)) * mu Set.univ

noncomputable def polynomialMomentsExponentialContract : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (H : X → ℝ), Measurable H → (∀ x, 0 ≤ H x) →
    ∀ (k : ℕ), 1 ≤ k → ∀ (C : ℝ), 0 < C →
    (∀ q : ℝ, 2 ≤ q →
      (∫⁻ x, ENNReal.ofReal (Real.rpow (H x) q) ∂mu) ≤
        ENNReal.ofReal (Real.rpow (C * q ^ k) q) * mu Set.univ) →
    (∫⁻ x, ENNReal.ofReal
      (Real.exp (Real.rpow (H x / (Real.exp 2 * C)) (1 / (k : ℝ))) - 1) ∂mu) ≤
      ENNReal.ofReal (Real.exp 4) * mu Set.univ

noncomputable def countableOverlapFiniteMomentContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i)))), G.Countable →
    ∀ (k : ℕ) (C : ℝ),
    (∀ (H : Finset G) (q : ℝ), 2 ≤ q →
      (∫⁻ x, (ENNReal.ofReal (finiteOverlap (H.image Subtype.val) x)) ^ q) ≤
        (ENNReal.ofReal (C * q ^ k)) ^ q *
          volume (finiteShadow (H.image Subtype.val))) →
    ∀ q : ℝ, 2 ≤ q →
    (∫⁻ x, (overlap G x) ^ q) ≤
      (ENNReal.ofReal (C * q ^ k)) ^ q * volume (shadow G)

noncomputable def countableOverlapTailExponentialContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i)))), G.Countable →
    volume (shadow G) < ∞ → ∀ (k : ℕ), 1 ≤ k → ∀ (C : ℝ), 0 < C →
    (∀ q : ℝ, 2 ≤ q →
      (∫⁻ x, (overlap G x) ^ q) ≤
        (ENNReal.ofReal (C * q ^ k)) ^ q * volume (shadow G)) →
    (∀ᵐ x ∂volume, overlap G x < ∞) ∧
      (∫⁻ x in shadow G, ENNReal.ofReal
        (Real.exp (Real.rpow ((overlap G x).toReal / (Real.exp 2 * C))
          (1 / (k : ℝ))) - 1)) ≤
        ENNReal.ofReal (Real.exp 4) * volume (shadow G)

end ReyZygmundVerification
