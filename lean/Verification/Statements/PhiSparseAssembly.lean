import ReyZygmund.Continuous.DyadicExtension
import ReyZygmund.Overlap.Countable

/-!
# Explicit sparse-Phi assembly propositions

Only the modules containing the family, rectangle, shadow and overlap
definitions are imported. Neither candidate assembly nor its theorem types
is imported or aliased. The main statement remains the independent challenge.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmundVerification

open ReyZygmund.Geometry ReyZygmund.Continuous ReyZygmund.Overlap

def phiSparseOverlapMomentsContract : Prop :=
  ∀ (n totalDim : ℕ), 2 ≤ n →
    ∃ K : ℝ, 0 < K ∧
      ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
        ∀ (D : ∀ i, DyadicGrid (d i)) (Phi : (Fin n → ℤ) → ℤ), Monotone Phi →
          ∀ (G : Set (∀ i, Box (Fin (d i)))), G ⊆ dyadicPhiRectangles D Phi →
            ∀ eta : ℝ, 0 < eta →
              ∀ E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ),
                (∀ R ∈ G, MeasurableSet (E R)) →
                (∀ R ∈ G, E R ⊆
                  (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) →
                Set.Pairwise G (fun R S => Disjoint (E R) (E S)) →
                (∀ R ∈ G, ENNReal.ofReal eta *
                  volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤
                    volume (E R)) →
                ∀ q : ℝ, 2 ≤ q →
                  (∫⁻ x, (overlap G x) ^ q ∂volume) ≤
                    (ENNReal.ofReal (K * eta⁻¹ * q ^ n)) ^ q * volume (shadow G)

def phiSparseOverlapExponentialContract : Prop :=
  ∀ (n totalDim : ℕ), 2 ≤ n →
    ∀ eta : ℝ, 0 < eta →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
          ∀ (D : ∀ i, DyadicGrid (d i)) (Phi : (Fin n → ℤ) → ℤ), Monotone Phi →
            ∀ (G : Set (∀ i, Box (Fin (d i)))), G ⊆ dyadicPhiRectangles D Phi →
              ∀ E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ),
                (∀ R ∈ G, MeasurableSet (E R)) →
                (∀ R ∈ G, E R ⊆
                  (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) →
                Set.Pairwise G (fun R S => Disjoint (E R) (E S)) →
                (∀ R ∈ G, ENNReal.ofReal eta *
                  volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤
                    volume (E R)) →
                volume (shadow G) < ∞ →
                (∀ᵐ x ∂volume, overlap G x < ∞) ∧
                  (∫⁻ x in shadow G, ENNReal.ofReal
                    (Real.exp (c * Real.rpow (overlap G x).toReal (1 / (n : ℝ))) - 1)
                      ∂volume) ≤ ENNReal.ofReal C * volume (shadow G)

end ReyZygmundVerification
