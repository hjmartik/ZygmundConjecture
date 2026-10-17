import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # The dimension constant in the maximal estimate

This constant is shared by the finite, global and sparse-overlap bounds.
-/

open scoped BigOperators

namespace ReyZygmund

variable {m : ℕ}

/-- The finite maximal estimate's dimension-only constant is uniform in the exponent,
top rectangle, smallest scales, family and input. -/
noncomputable def maximalDimensionConstant (d : Fin m → ℕ) : ℝ :=
  (2 * (1 + ((m : ℝ) * (2 : ℝ) ^ m *
      ((2 : ℝ) ^ (6 * (∑ i, d i) + 10) + (2 : ℝ) ^ (m - 1))) *
    (1 + Real.sqrt ((m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)))))) ^ 2

end ReyZygmund
