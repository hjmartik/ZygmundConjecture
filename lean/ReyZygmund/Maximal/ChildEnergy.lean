import ReyZygmund.Geometry.ProductChildren
import ReyZygmund.Geometry.ProductIntegrability
import Mathlib.MeasureTheory.Measure.Real

/-! # Childwise energy outside a small-density set

The full product difference is constant on each product of children. The parent
density assumption removes at most half of each child's volume. Summing the
integrals over this partition gives the factor-two energy estimate.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem child_complement_volume
    (Q R : ∀ i, Box (Fin (d i))) (hR : R ∈ productLeaves Q (fun _ => 1))
    (E : Set (ProductPoint d)) (hE : MeasurableSet E)
    (hden : volume.real (productRectangle Q ∩ E) ≤
      (1 / (2 : ℝ) ^ ((∑ i, d i) + 1)) * volume.real (productRectangle Q)) :
    volume.real (productRectangle R) ≤ 2 * volume.real (productRectangle R \ E) := by
  have hQfin : volume (productRectangle Q ∩ E) ≠ ∞ :=
    measure_ne_top_of_subset Set.inter_subset_left
      (productRectangle_volume_lt_top Q).ne
  have hinter : volume.real (productRectangle R ∩ E) ≤ volume.real (productRectangle Q ∩ E) :=
    measureReal_mono (fun _ hx => ⟨productLeaves_subset hR hx.1, hx.2⟩) hQfin
  have hhalf : (1 / (2 : ℝ) ^ ((∑ i, d i) + 1)) * volume.real (productRectangle Q) =
      volume.real (productRectangle R) / 2 := by
    rw [product_child_volume Q R hR, pow_succ]
    field_simp
  have hsmall : volume.real (productRectangle R ∩ E) ≤ volume.real (productRectangle R) / 2 :=
    (hinter.trans hden).trans_eq hhalf
  have hsplit := measureReal_inter_add_sdiff (μ := volume) (s := productRectangle R)
    hE (productRectangle_volume_lt_top R).ne
  linarith

private theorem integral_productLeaves_sdiff
    (Q : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (E : Set (ProductPoint d)) (hE : MeasurableSet E)
    (f : ProductPoint d → ℝ) (hf : IntegrableOn f (productRectangle Q) volume) :
    (∫ x in (productRectangle Q \ E), f x) =
      ∑ R ∈ productLeaves Q N, ∫ x in (productRectangle R \ E), f x := by
  have hcover : productRectangle Q \ E = ⋃ R ∈ productLeaves Q N, productRectangle R \ E := by
    ext x
    constructor
    · intro hx
      obtain ⟨R, hR, hxR⟩ := productLeaves_cover Q N x hx.1
      exact Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨hR, ⟨hxR, hx.2⟩⟩⟩
    · intro hx
      obtain ⟨R, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hR, hxR⟩ := Set.mem_iUnion.mp hx
      exact ⟨productLeaves_subset hR hxR.1, hxR.2⟩
  rw [hcover]
  apply integral_biUnion_finset
  · intro R _
    exact (measurableSet_productRectangle R).diff hE
  · intro R hR S hS hne
    apply Set.disjoint_left.mpr
    intro x hxR hxS
    exact hne (productLeaves_unique hR hS hxR.1 hxS.1)
  · intro R hR
    exact hf.mono_set (fun _ hx => productLeaves_subset hR hx.1)

/-- Small density in the parent removes at most half of each child's
volume. Constancy of the full difference gives the factor-two energy comparison. -/
theorem productDifference_child_energy
    (Q : ∀ i, Box (Fin (d i))) (F : boundedMeasurableFunctions d)
    (E : Set (ProductPoint d)) (hE : MeasurableSet E)
    (hden : volume.real (productRectangle Q ∩ E) ≤
      (1 / (2 : ℝ) ^ ((∑ i, d i) + 1)) * volume.real (productRectangle Q)) :
    (∫ x in productRectangle Q, ((productDifferenceMap Finset.univ Q F).1 x) ^ 2) ≤
      2 * (∫ x in (productRectangle Q \ E), ((productDifferenceMap Finset.univ Q F).1 x) ^ 2) := by
  let f : ProductPoint d → ℝ := fun x => ((productDifferenceMap Finset.univ Q F).1 x) ^ 2
  have hconst : ProductLeafConstant Q (fun _ => 1) f := by
    intro R hR x hx y hy
    exact congrArg (fun t : ℝ => t ^ 2)
      (productDifference_constant_on_child Q R hR F x hx y hy)
  have hfi := integrableOn_productLeafConstant Q (fun _ => 1) f hconst
  have hroot : (∫ x in productRectangle Q, f x) =
      ∑ R ∈ productLeaves Q (fun _ => 1), ∫ x in productRectangle R, f x := by
    simpa only [Set.sdiff_empty] using
      integral_productLeaves_sdiff Q (fun _ => 1) ∅ MeasurableSet.empty f hfi
  change (∫ x in productRectangle Q, f x) ≤ 2 * (∫ x in (productRectangle Q \ E), f x)
  rw [hroot, integral_productLeaves_sdiff Q (fun _ => 1) E hE f hfi, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro R hR
  have hcorner : (fun i => (R i).upper) ∈ productRectangle R :=
    (mem_productRectangle R _).mpr (fun i => (R i).upper_mem)
  have heq : ∀ x ∈ productRectangle R, f x = f (fun i => (R i).upper) :=
    fun x hx => hconst R hR x hx _ hcorner
  have hfull : (∫ x in productRectangle R, f x) =
      volume.real (productRectangle R) * f (fun i => (R i).upper) := by
    calc
      _ = ∫ _ in productRectangle R, f (fun i => (R i).upper) :=
        setIntegral_congr_fun (measurableSet_productRectangle R) heq
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  have hpart : (∫ x in (productRectangle R \ E), f x) =
      volume.real (productRectangle R \ E) * f (fun i => (R i).upper) := by
    calc
      _ = ∫ _ in (productRectangle R \ E), f (fun i => (R i).upper) :=
        setIntegral_congr_fun ((measurableSet_productRectangle R).diff hE)
          (fun x hx => heq x hx.1)
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  rw [hfull, hpart]
  have hc : 0 ≤ f (fun i => (R i).upper) := sq_nonneg _
  calc
    _ ≤ (2 * volume.real (productRectangle R \ E)) * f (fun i => (R i).upper) :=
      mul_le_mul_of_nonneg_right (child_complement_volume Q R hR E hE hden) hc
    _ = _ := by ring

end ReyZygmund
