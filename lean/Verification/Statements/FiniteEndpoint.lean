import ReyZygmund.Selection.Endpoint

/-! Explicit finite high-average endpoint shadow proposition. -/

open BoxIntegral MeasureTheory
open ReyZygmund.Geometry ReyZygmund.Overlap
open scoped BigOperators ENNReal Classical

namespace ReyZygmundVerification

def finiteRoundedEndpointContract : Prop :=
  ∀ (n : ℕ) (d : Fin (n + 1) → ℕ), 2 ≤ n → (∀ i, 0 < d i) →
    ∃ C : ℝ, 0 < C ∧
      ∀ (D : ∀ i, DyadicGrid (d i))
        (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)), Monotone phi →
      ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
      ∀ (lam : ℝ), 0 < lam → ∀ F : Finset (∀ i, Box (Fin (d i))),
      (↑F : Set (∀ i, Box (Fin (d i)))) ⊆ roundedGridRectangles D phi →
      (∀ R ∈ F, lam <
        (∫ x in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), |f x|) /
          volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) →
      volume (finiteShadow F) ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
        (|f x| / lam * (Real.log (Real.exp 1 + |f x| / lam)) ^ (n - 1))

end ReyZygmundVerification
