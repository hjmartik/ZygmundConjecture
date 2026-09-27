import ReyZygmund.Maximal.EndpointExhaustion

/-! Explicit expected propositions for strict-level finite-shadow exhaustion. -/

open BoxIntegral MeasureTheory
open ReyZygmund ReyZygmund.Geometry ReyZygmund.Overlap
open scoped BigOperators Classical ENNReal

namespace ReyZygmundVerification

def euclideanLevelsetUnionContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (lam : ℝ), 0 < lam →
    {x | ENNReal.ofReal lam < euclideanFamilyMaximal G f x} =
      ⋃ R ∈ G, ⋃ (_ : lam <
        (∫ y in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), |f y|) /
          volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))),
        (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))

def euclideanLevelsetFiniteShadowsContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i)))), G.Countable →
    ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ) (lam : ℝ), 0 < lam →
    ∀ C : ℝ≥0∞,
      (∀ F : Finset (∀ i, Box (Fin (d i))),
        (↑F : Set (∀ i, Box (Fin (d i)))) ⊆ G →
        (∀ R ∈ F, lam <
          (∫ y in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), |f y|) /
            volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) →
        volume (finiteShadow F) ≤ C) →
      volume {x | ENNReal.ofReal lam < euclideanFamilyMaximal G f x} ≤ C

end ReyZygmundVerification
