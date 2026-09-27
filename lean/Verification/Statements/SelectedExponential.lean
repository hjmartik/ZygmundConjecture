import ReyZygmund.Selection.Exponential

/-! Explicit selected-family exponential proposition. -/

open BoxIntegral MeasureTheory
open ReyZygmund.Geometry ReyZygmund.Overlap
open scoped BigOperators ENNReal Classical

namespace ReyZygmundVerification

def selectedRoundedExponentialContract : Prop :=
  ∀ (n : ℕ) (d : Fin (n + 1) → ℕ), 2 ≤ n → (∀ i, 0 < d i) →
    ∃ c B : ℝ, 0 < c ∧ 0 < B ∧
      ∀ (D : ∀ i, DyadicGrid (d i))
        (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)), Monotone phi →
      ∀ G : Finset (∀ i, Box (Fin (d i))),
      (↑G : Set (∀ i, Box (Fin (d i)))) ⊆ roundedGridRectangles D phi →
      (∀ R ∈ G,
        volume.real ((flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ∩
          finiteShadow (G.erase R)) ≤
          (1 / 2 : ℝ) * volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) →
      (∫⁻ x in finiteShadow G, ENNReal.ofReal
        (Real.exp (c * Real.rpow (finiteOverlap G x) (1 / ((n - 1 : ℕ) : ℝ))))) ≤
        ENNReal.ofReal B * volume (finiteShadow G)

end ReyZygmundVerification
