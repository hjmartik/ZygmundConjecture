import ReyZygmund.Geometry.GridFamilies
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Data.List.FinRange

/-! # Coordinate maximal functions on the full dyadic grids

The coordinate averages and their composition take extended nonnegative
values. No cutoff or finite-integral convention enters these definitions.
The signed-input application starts with `ENNReal.ofReal |f x|`.
-/

open BoxIntegral MeasureTheory
open scoped ENNReal Classical

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- The normalized integral over a single coordinate cube. -/
noncomputable def coordinateGridAverage (j : Fin m) (Q : Box (Fin (d j)))
    (F : ProductPoint d → ℝ≥0∞) (x : ProductPoint d) : ℝ≥0∞ :=
  {x | x j ∈ (Q : Set (Fin (d j) → ℝ))}.indicator
    (fun x => (volume (Q : Set (Fin (d j) → ℝ)))⁻¹ *
      ∫⁻ y in (Q : Set (Fin (d j) → ℝ)), F (Function.update x j y)) x

/-- The maximum over every cube of the specified coordinate grid. -/
noncomputable def coordinateGridMaximal (D : ∀ i, DyadicGrid (d i))
    (j : Fin m) (F : ProductPoint d → ℝ≥0∞) (x : ProductPoint d) : ℝ≥0∞ :=
  ⨆ Q : {Q : Box (Fin (d j)) | ∃ n : ℤ, Q ∈ (D j).cubes n},
    coordinateGridAverage j Q.1 F x

/-- Ordered composition `M₀ (M₁ (... Mₘ₋₁ F))` of the grid operators. -/
noncomputable def iteratedGridMaximal (D : ∀ i, DyadicGrid (d i))
    (F : ProductPoint d → ℝ≥0∞) : ProductPoint d → ℝ≥0∞ :=
  (List.finRange m).foldr (fun j H => coordinateGridMaximal D j H) F

end ReyZygmund
