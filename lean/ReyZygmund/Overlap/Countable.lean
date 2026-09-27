import ReyZygmund.Overlap.Finite
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Countable overlaps as increasing limits of finite overlaps

The overlap is an extended nonnegative sum. No finiteness or integrability
is imposed through the definition, and no infinite real sum is totalized.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Overlap

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

def shadow (G : Set (∀ i, Box (Fin (d i)))) : Set (Fin (∑ i, d i) → ℝ) :=
  ⋃ R ∈ G, (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))

noncomputable def overlap (G : Set (∀ i, Box (Fin (d i))))
    (x : Fin (∑ i, d i) → ℝ) : ℝ≥0∞ :=
  ∑' R : G, (flatProductBox R.1 : Set (Fin (∑ i, d i) → ℝ)).indicator
    (fun _ => (1 : ℝ≥0∞)) x

theorem measurableSet_shadow
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G.Countable) : MeasurableSet (shadow G) :=
  MeasurableSet.biUnion hG (fun R _ => (flatProductBox R).measurableSet_coe)

theorem finiteShadow_subset_shadow
    (G : Set (∀ i, Box (Fin (d i)))) (H : Finset G) :
    finiteShadow (H.image Subtype.val) ⊆ shadow G := by
  intro x hx
  obtain ⟨R, hR, hxR⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp hR
  exact Set.mem_iUnion₂.mpr ⟨S.1, S.2, hxR⟩

theorem overlap_eq_iSup_finset
    (G : Set (∀ i, Box (Fin (d i)))) (x : Fin (∑ i, d i) → ℝ) :
    overlap G x = ⨆ H : Finset G,
      ENNReal.ofReal (finiteOverlap (H.image Subtype.val) x) := by
  rw [overlap, ENNReal.tsum_eq_iSup_sum]
  congr 1
  funext H
  rw [finiteOverlap, Finset.sum_image (fun _ _ _ _ h => Subtype.ext h),
    ENNReal.ofReal_sum_of_nonneg (fun R _ => Set.indicator_nonneg (fun _ _ => zero_le_one) x)]
  apply Finset.sum_congr rfl
  intro R _
  by_cases hx : x ∈ (flatProductBox R.1 : Set _)
  · simp only [Set.indicator_of_mem hx, ENNReal.ofReal_one]
  · simp only [Set.indicator_of_notMem hx, ENNReal.ofReal_zero]

theorem measurable_overlap
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G.Countable) : Measurable (overlap G) := by
  have := hG.to_subtype
  have heq : overlap G = fun x => ⨆ H : Finset G,
      ENNReal.ofReal (finiteOverlap (H.image Subtype.val) x) :=
    funext (overlap_eq_iSup_finset G)
  rw [heq]
  exact Measurable.iSup (fun H : Finset G =>
    (measurable_finiteOverlap (H.image Subtype.val)).ennreal_ofReal)

theorem overlap_eq_zero_of_not_mem
    (G : Set (∀ i, Box (Fin (d i)))) (x : Fin (∑ i, d i) → ℝ)
    (hx : x ∉ shadow G) : overlap G x = 0 := by
  have hz (R : G) : (flatProductBox R.1 : Set (Fin (∑ i, d i) → ℝ)).indicator
      (fun _ => (1 : ℝ≥0∞)) x = 0 :=
    Set.indicator_of_notMem (fun h => hx (Set.mem_iUnion₂.mpr ⟨R.1, R.2, h⟩)) _
  simp only [overlap, hz, tsum_zero]

theorem lintegral_overlap_rpow_eq_iSup
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G.Countable)
    (q : ℝ) (hq : 0 < q) :
    (∫⁻ x, (overlap G x) ^ q) =
      ⨆ H : Finset G, ∫⁻ x,
        (ENNReal.ofReal (finiteOverlap (H.image Subtype.val) x)) ^ q := by
  have := hG.to_subtype
  let F (H : Finset G) (x : Fin (∑ i, d i) → ℝ) : ℝ≥0∞ :=
    (ENNReal.ofReal (finiteOverlap (H.image Subtype.val) x)) ^ q
  have hmeas (H : Finset G) : Measurable (F H) :=
    (measurable_finiteOverlap (H.image Subtype.val)).ennreal_ofReal.pow_const q
  have hmono : Monotone F := by
    intro H K hHK x
    apply ENNReal.rpow_le_rpow _ hq.le
    apply ENNReal.ofReal_le_ofReal
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_mono Subtype.val hHK)
      (fun _ _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
  have hdir : Directed (· ≤ ·) F := fun H K =>
    ⟨H ∪ K, hmono Finset.subset_union_left, hmono Finset.subset_union_right⟩
  have heq (x : Fin (∑ i, d i) → ℝ) :
      (overlap G x) ^ q = ⨆ H : Finset G, F H x := by
    rw [overlap_eq_iSup_finset]
    exact (ENNReal.orderIsoRpow q hq).map_iSup
      (fun H : Finset G => ENNReal.ofReal (finiteOverlap (H.image Subtype.val) x))
  calc
    _ = ∫⁻ x, ⨆ H : Finset G, F H x := lintegral_congr heq
    _ = _ := lintegral_iSup_directed_of_measurable hmeas hdir

end ReyZygmund.Overlap
