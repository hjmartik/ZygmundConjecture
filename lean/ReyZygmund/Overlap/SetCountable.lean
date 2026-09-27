import ReyZygmund.Overlap.SetFinite
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Countable measurable-set overlaps

The nonnegative series is the increasing supremum of finite overlaps.
No spatial boundedness or almost-everywhere finiteness is assumed in this passage.
-/

open MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Overlap

variable {d : ℕ}

theorem measurableSet_setShadow (G : Set (Set (Fin d → ℝ)))
    (hG : G.Countable) (hm : ∀ I ∈ G, MeasurableSet I) :
    MeasurableSet (setShadow G) :=
  MeasurableSet.biUnion hG hm

theorem finiteSetShadow_subset_setShadow
    (G : Set (Set (Fin d → ℝ))) (H : Finset G) :
    finiteSetShadow (H.image Subtype.val) ⊆ setShadow G := by
  intro x hx
  obtain ⟨I, hI, hxI⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hI
  exact Set.mem_iUnion₂.mpr ⟨J.1, J.2, hxI⟩

theorem setOverlap_eq_iSup_finset
    (G : Set (Set (Fin d → ℝ))) (x : Fin d → ℝ) :
    setOverlap G x = ⨆ H : Finset G,
      ENNReal.ofReal (finiteSetOverlap (H.image Subtype.val) x) := by
  rw [setOverlap, ENNReal.tsum_eq_iSup_sum]
  congr 1
  funext H
  rw [finiteSetOverlap, Finset.sum_image (fun _ _ _ _ h => Subtype.ext h),
    ENNReal.ofReal_sum_of_nonneg (fun I _ =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) x)]
  apply Finset.sum_congr rfl
  intro I _
  by_cases hx : x ∈ I.1
  · simp only [Set.indicator_of_mem hx, ENNReal.ofReal_one]
  · simp only [Set.indicator_of_notMem hx, ENNReal.ofReal_zero]

theorem measurable_setOverlap (G : Set (Set (Fin d → ℝ)))
    (hG : G.Countable) (hm : ∀ I ∈ G, MeasurableSet I) :
    Measurable (setOverlap G) := by
  have := hG.to_subtype
  have heq : setOverlap G = fun x => ⨆ H : Finset G,
      ENNReal.ofReal (finiteSetOverlap (H.image Subtype.val) x) :=
    funext (setOverlap_eq_iSup_finset G)
  rw [heq]
  apply Measurable.iSup
  intro H
  apply (measurable_finiteSetOverlap (H.image Subtype.val) _).ennreal_ofReal
  intro I hI
  obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hI
  exact hm J.1 J.2

theorem setOverlap_eq_zero_of_not_mem
    (G : Set (Set (Fin d → ℝ))) (x : Fin d → ℝ)
    (hx : x ∉ setShadow G) : setOverlap G x = 0 := by
  have hz (I : G) : I.1.indicator (fun _ => (1 : ℝ≥0∞)) x = 0 :=
    Set.indicator_of_notMem (fun h => hx (Set.mem_iUnion₂.mpr ⟨I.1, I.2, h⟩)) _
  simp only [setOverlap, hz, tsum_zero]

theorem lintegral_setOverlap_rpow_eq_iSup
    (G : Set (Set (Fin d → ℝ))) (hG : G.Countable)
    (hm : ∀ I ∈ G, MeasurableSet I) (q : ℝ) (hq : 0 < q) :
    (∫⁻ x, (setOverlap G x) ^ q) =
      ⨆ H : Finset G, ∫⁻ x,
        (ENNReal.ofReal (finiteSetOverlap (H.image Subtype.val) x)) ^ q := by
  have := hG.to_subtype
  let F (H : Finset G) (x : Fin d → ℝ) : ℝ≥0∞ :=
    (ENNReal.ofReal (finiteSetOverlap (H.image Subtype.val) x)) ^ q
  have hmeas (H : Finset G) : Measurable (F H) := by
    apply (measurable_finiteSetOverlap (H.image Subtype.val) _).ennreal_ofReal.pow_const q
    intro I hI
    obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hI
    exact hm J.1 J.2
  have hmono : Monotone F := by
    intro H K hHK x
    apply ENNReal.rpow_le_rpow _ hq.le
    apply ENNReal.ofReal_le_ofReal
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_mono Subtype.val hHK)
      (fun _ _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
  have hdir : Directed (· ≤ ·) F := fun H K =>
    ⟨H ∪ K, hmono Finset.subset_union_left, hmono Finset.subset_union_right⟩
  have heq (x : Fin d → ℝ) :
      (setOverlap G x) ^ q = ⨆ H : Finset G, F H x := by
    rw [setOverlap_eq_iSup_finset]
    exact (ENNReal.orderIsoRpow q hq).map_iSup
      (fun H : Finset G => ENNReal.ofReal (finiteSetOverlap (H.image Subtype.val) x))
  calc
    _ = ∫⁻ x, ⨆ H : Finset G, F H x := lintegral_congr heq
    _ = _ := lintegral_iSup_directed_of_measurable hmeas hdir

/-- A uniform finite-family moment bound passes to the countable sum.
The bound is on the full shadow; no enumeration changes the overlap. -/
theorem countable_set_moment_of_finite
    (G : Set (Set (Fin d → ℝ))) (hG : G.Countable)
    (hm : ∀ I ∈ G, MeasurableSet I) (q : ℝ) (hq : 0 < q) (C : ℝ≥0∞)
    (hfinite : ∀ H : Finset G,
      (∫⁻ x, (ENNReal.ofReal (finiteSetOverlap (H.image Subtype.val) x)) ^ q) ≤
        C * volume (finiteSetShadow (H.image Subtype.val))) :
    (∫⁻ x, (setOverlap G x) ^ q) ≤ C * volume (setShadow G) := by
  rw [lintegral_setOverlap_rpow_eq_iSup G hG hm q hq]
  apply iSup_le
  intro H
  exact (hfinite H).trans (mul_le_mul' le_rfl
    (measure_mono (finiteSetShadow_subset_setShadow G H)))

end ReyZygmund.Overlap
