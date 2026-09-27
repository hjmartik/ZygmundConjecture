import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Overlaps of measurable-set families

The finite overlap is real-valued; the countable overlap uses extended
nonnegative summation. The definitions impose no geometric assumptions.
-/

open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.Overlap

def finiteSetShadow {d : ℕ} (H : Finset (Set (Fin d → ℝ))) : Set (Fin d → ℝ) :=
  ⋃ I ∈ H, I

noncomputable def finiteSetOverlap {d : ℕ} (H : Finset (Set (Fin d → ℝ)))
    (x : Fin d → ℝ) : ℝ :=
  ∑ I ∈ H, I.indicator (fun _ => 1) x

def setShadow {d : ℕ} (G : Set (Set (Fin d → ℝ))) : Set (Fin d → ℝ) :=
  ⋃ I ∈ G, I

noncomputable def setOverlap {d : ℕ} (G : Set (Set (Fin d → ℝ)))
    (x : Fin d → ℝ) : ℝ≥0∞ :=
  ∑' I : G, I.1.indicator (fun _ => (1 : ℝ≥0∞)) x

end ReyZygmund.Overlap
