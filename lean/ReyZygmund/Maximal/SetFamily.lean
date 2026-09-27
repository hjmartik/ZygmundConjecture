import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! # Maximal averages over measurable sets

Nonnegative integration defines the averages and their supremum, including
infinite values. Measurability of the sets and positivity and finiteness of their
measures are hypotheses of the relevant theorems.

-/

open MeasureTheory
open scoped ENNReal

namespace ReyZygmund

/-- Supremum of normalized nonnegative integrals over the supplied
sets. Each average is supported on its indexing set. -/
noncomputable def setFamilyMaximal {d : ℕ}
    (E : Set (Set (Fin d → ℝ))) (f : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) : ℝ≥0∞ :=
  ⨆ I : E, I.1.indicator
    (fun _ => (∫⁻ y in I.1, ENNReal.ofReal |f y|) / volume I.1) x

end ReyZygmund
