import ReyZygmund.Overlap.Exponential

/-! Explicit dimensional sparse-overlap exponential proposition. -/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal

open ReyZygmund.MathlibOnly (CubeGrid gridRectangles)

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry ReyZygmund.Overlap

def weakerSparseOverlapExponentialContract : Prop :=
    ∃ c B : ℕ → ℕ → ℝ,
      (∀ m D, 0 < c m D) ∧ (∀ m D, 0 < B m D) ∧
      ∀ (m : ℕ) (d : Fin m → ℕ), 2 ≤ m → (∀ i, 0 < d i) →
      ∀ (D : ∀ i, CubeGrid (d i)) (G : Set (∀ i, Box (Fin (d i)))),
      G ⊆ gridRectangles D →
      (∀ R ∈ G, ∀ S ∈ G, productRectangle R ⊆ productRectangle S → ∃ i, R i = S i) →
      ∀ eta : ℝ, 0 < eta →
      ∀ E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ),
      (∀ R ∈ G, NullMeasurableSet (E R) volume) →
      (∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) →
      Set.Pairwise G (fun R S => Disjoint (E R) (E S)) →
      (∀ R ∈ G, ENNReal.ofReal eta *
        volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤ volume (E R)) →
      volume (shadow G) < ∞ →
      (∫⁻ x in shadow G, ENNReal.ofReal
        (Real.exp (c m (∑ i, d i) *
          Real.rpow (eta * (overlap G x).toReal) (1 / ((m - 1 : ℕ) : ℝ))) - 1)) ≤
        ENNReal.ofReal (B m (∑ i, d i)) * volume (shadow G)

end ReyZygmundVerification
