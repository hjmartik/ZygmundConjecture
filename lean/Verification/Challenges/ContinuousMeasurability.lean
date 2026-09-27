import Verification.Challenges.Endpoints

/-! # Continuous maximal measurability statements

Translation of rectangles gives open level sets, including at points on their
faces. Only positivity of side lengths is required, not monotonicity or other
regularity of the side function.

The imported `endpointMaximal` is the extended supremum of supported averages of
`|f|`. No endpoint or measurability proof is imported. The statements allow
arbitrary coordinate dimensions, extending the paper's positive-dimensional,
at-least-three-parameter setting.

-/

open MeasureTheory ReyZygmund.Geometry
open scoped BigOperators ENNReal

namespace ReyZygmundVerification.Challenges

/-- Every strict extended-valued level is open for the all-position
family, including threshold zero and the empty level above infinity. -/
def continuousMaximalOpenLevelStatement : Prop :=
  ∀ (n : ℕ) (d : Fin (n + 1) → ℕ)
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    ∀ a : ℝ≥0∞,
      IsOpen {x | a < endpointMaximal (continuousPhiRectangles d phi) f x}

/-- Measurability of the continuous supremum, not merely of an
almost-everywhere representative or of a measurable dominating function. -/
def continuousMaximalMeasurableStatement : Prop :=
  ∀ (n : ℕ) (d : Fin (n + 1) → ℕ)
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    Measurable (endpointMaximal (continuousPhiRectangles d phi) f)

end ReyZygmundVerification.Challenges
