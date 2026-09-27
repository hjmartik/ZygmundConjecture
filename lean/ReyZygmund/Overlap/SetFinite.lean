import ReyZygmund.Overlap.SetDefinitions
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # Finite overlaps without rectangle assumptions

These elementary facts use only measurable sets of finite measure. In
particular, none of the sets needs to be bounded or to be a rectangle.
-/

open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.Overlap

theorem subset_finiteSetShadow {d : ℕ} (H : Finset (Set (Fin d → ℝ)))
    (I : Set (Fin d → ℝ)) (hI : I ∈ H) : I ⊆ finiteSetShadow H :=
  Set.subset_iUnion_of_subset I (Set.subset_iUnion_of_subset hI Set.Subset.rfl)

theorem measurableSet_finiteSetShadow {d : ℕ} (H : Finset (Set (Fin d → ℝ)))
    (hm : ∀ I ∈ H, MeasurableSet I) : MeasurableSet (finiteSetShadow H) :=
  Finset.measurableSet_biUnion H hm

theorem volume_finiteSetShadow_lt_top {d : ℕ} (H : Finset (Set (Fin d → ℝ)))
    (hf : ∀ I ∈ H, volume I < ∞) : volume (finiteSetShadow H) < ∞ :=
  measure_biUnion_lt_top H.finite_toSet hf

theorem measurable_finiteSetOverlap {d : ℕ} (H : Finset (Set (Fin d → ℝ)))
    (hm : ∀ I ∈ H, MeasurableSet I) : Measurable (finiteSetOverlap H) :=
  Finset.measurable_sum H (fun I hI => measurable_const.indicator (hm I hI))

theorem finiteSetOverlap_nonneg {d : ℕ} (H : Finset (Set (Fin d → ℝ)))
    (x : Fin d → ℝ) : 0 ≤ finiteSetOverlap H x :=
  Finset.sum_nonneg (fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) x)

theorem finiteSetOverlap_le_card {d : ℕ} (H : Finset (Set (Fin d → ℝ)))
    (x : Fin d → ℝ) : finiteSetOverlap H x ≤ H.card := by
  calc
    _ ≤ ∑ _I ∈ H, (1 : ℝ) := Finset.sum_le_sum (fun I _ => by
      by_cases hx : x ∈ I
      · simp only [Set.indicator_of_mem hx, le_refl]
      · simp only [Set.indicator_of_notMem hx, zero_le_one])
    _ = _ := by simp

theorem finiteSetOverlap_eq_zero_of_not_mem {d : ℕ}
    (H : Finset (Set (Fin d → ℝ))) (x : Fin d → ℝ)
    (hx : x ∉ finiteSetShadow H) : finiteSetOverlap H x = 0 := by
  apply Finset.sum_eq_zero
  intro I hI
  exact Set.indicator_of_notMem (fun h => hx (subset_finiteSetShadow H I hI h)) _

theorem memLp_finiteSetOverlap {d : ℕ} (H : Finset (Set (Fin d → ℝ)))
    (hm : ∀ I ∈ H, MeasurableSet I) (hf : ∀ I ∈ H, volume I < ∞)
    (p : ℝ≥0∞) : MemLp (finiteSetOverlap H) p volume := by
  apply memLp_finsetSum
  intro I hI
  exact memLp_indicator_const p (hm I hI) 1 (Or.inr (hf I hI).ne)

theorem integrable_rpow_finiteSetOverlap {d : ℕ} (H : Finset (Set (Fin d → ℝ)))
    (hm : ∀ I ∈ H, MeasurableSet I) (hf : ∀ I ∈ H, volume I < ∞)
    (q : ℝ) (hq : 0 < q) :
    Integrable (fun x => Real.rpow (finiteSetOverlap H x) q) volume := by
  have h := (memLp_finiteSetOverlap H hm hf (ENNReal.ofReal q)).integrable_norm_rpow
    (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top
  simpa only [Real.norm_eq_abs, abs_of_nonneg (finiteSetOverlap_nonneg H _),
    ENNReal.toReal_ofReal hq.le, Real.rpow_eq_pow] using h

end ReyZygmund.Overlap
