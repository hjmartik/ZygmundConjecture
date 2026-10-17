import ReyZygmund.ToMathlib.Order.Indicator
import ReyZygmund.MathlibOnly.Definitions

/-! # Indicator formulas for maximal functions

The supremum of averages over rectangles containing a point equals the
supremum of their indicator-supported averages.
-/

open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.MathlibOnly

/-- The maximal function as a supremum of indicator-supported averages. -/
theorem maximal_eq_iSup_indicator {m : ℕ} {d : Fin m → ℕ}
    (G : Set (Rectangle d)) (f : Point d → ℝ) :
    maximal G f = fun x => ⨆ R : G, (rectangle R.1).indicator
      (fun _ => (∫⁻ y in rectangle R.1, ENNReal.ofReal |f y| ∂volume) /
        volume (rectangle R.1)) x := by
  funext x
  exact ENNReal.iSup_mem_eq_iSup_indicator G rectangle
    (fun R => (∫⁻ y in rectangle R, ENNReal.ofReal |f y| ∂volume) /
      volume (rectangle R)) x

/-- The same indicator formula for lower-inclusive rectangles. -/
theorem maximalIco_eq_iSup_indicator {m : ℕ} {d : Fin m → ℕ}
    (G : Set (Rectangle d)) (f : Point d → ℝ) :
    maximalIco G f = fun x => ⨆ R : G, (rectangleIco R.1).indicator
      (fun _ => (∫⁻ y in rectangleIco R.1, ENNReal.ofReal |f y| ∂volume) /
        volume (rectangleIco R.1)) x := by
  funext x
  exact ENNReal.iSup_mem_eq_iSup_indicator G rectangleIco
    (fun R => (∫⁻ y in rectangleIco R, ENNReal.ofReal |f y| ∂volume) /
      volume (rectangleIco R)) x

end ReyZygmund.MathlibOnly
