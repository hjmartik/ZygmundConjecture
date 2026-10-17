import Mathlib.Basic.ENNReal.Basic
import Mathlib.Algebra.Order.Group.Indicator

/-! # Supremum of nonnegative functions supported on sets -/

open scoped ENNReal Classical

namespace ENNReal

/-- Restricting a nonnegative supremum to sets containing the point is the same
as extending each term by zero outside its set. -/
theorem iSup_mem_eq_iSup_indicator {α β : Type*}
    (G : Set α) (sets : α → Set β) (a : α → ℝ≥0∞) (x : β) :
    (⨆ R ∈ G, ⨆ (_ : x ∈ sets R), a R) =
      ⨆ R : G, (sets R.1).indicator (fun _ => a R.1) x := by
  apply le_antisymm
  · refine iSup_le fun R => iSup_le fun hR => iSup_le fun hx => ?_
    calc
      a R = (sets R).indicator (fun _ => a R) x :=
        (Set.indicator_of_mem hx (fun _ : β => a R)).symm
      _ ≤ ⨆ R : G, (sets R.1).indicator (fun _ => a R.1) x :=
        le_iSup (fun S : G => (sets S.1).indicator (fun _ => a S.1) x) ⟨R, hR⟩
  · refine iSup_le fun R => ?_
    by_cases hx : x ∈ sets R.1
    · rw [Set.indicator_of_mem hx]
      exact le_iSup_of_le R.1 (le_iSup_of_le R.2 (le_iSup_of_le hx le_rfl))
    · rw [Set.indicator_of_notMem hx]
      exact bot_le

end ENNReal
