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

private theorem childEnergy_productBox_volume_lt_top (Q : ∀ i, Box (Fin (d i))) :
    volume (productBox Q) < ∞ := by
  change Measure.pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
    (Set.pi Set.univ (fun i => (Q i : Set (Fin (d i) → ℝ)))) < ∞
  rw [Measure.pi_pi]
  exact ENNReal.prod_lt_top (fun i _ => (Q i).measure_coe_lt_top volume)

private theorem child_complement_volume
    (Q R : ∀ i, Box (Fin (d i))) (hR : R ∈ productLeaves Q (fun _ => 1))
    (E : Set (ProductPoint d)) (hE : MeasurableSet E)
    (hden : volume.real (productBox Q ∩ E) ≤
      (1 / (2 : ℝ) ^ ((∑ i, d i) + 1)) * volume.real (productBox Q)) :
    volume.real (productBox R) ≤ 2 * volume.real (productBox R \ E) := by
  have hQfin : volume (productBox Q ∩ E) ≠ ∞ :=
    measure_ne_top_of_subset Set.inter_subset_left
      (childEnergy_productBox_volume_lt_top Q).ne
  have hinter : volume.real (productBox R ∩ E) ≤ volume.real (productBox Q ∩ E) :=
    measureReal_mono (fun _ hx => ⟨productLeaves_subset hR hx.1, hx.2⟩) hQfin
  have hhalf : (1 / (2 : ℝ) ^ ((∑ i, d i) + 1)) * volume.real (productBox Q) =
      volume.real (productBox R) / 2 := by
    rw [product_child_volume Q R hR, pow_succ]
    field_simp
  have hsmall : volume.real (productBox R ∩ E) ≤ volume.real (productBox R) / 2 :=
    (hinter.trans hden).trans_eq hhalf
  have hsplit := measureReal_inter_add_sdiff (μ := volume) (s := productBox R)
    hE (childEnergy_productBox_volume_lt_top R).ne
  linarith

private theorem integral_productLeaves_sdiff
    (Q : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (E : Set (ProductPoint d)) (hE : MeasurableSet E)
    (f : ProductPoint d → ℝ) (hf : IntegrableOn f (productBox Q) volume) :
    (∫ x in (productBox Q \ E), f x) =
      ∑ R ∈ productLeaves Q N, ∫ x in (productBox R \ E), f x := by
  have hcover : productBox Q \ E = ⋃ R ∈ productLeaves Q N, productBox R \ E := by
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
    exact (measurableSet_productBox R).diff hE
  · intro R hR S hS hne
    apply Set.disjoint_left.mpr
    intro x hxR hxS
    exact hne (productLeaves_unique hR hS hxR.1 hxS.1)
  · intro R hR
    exact hf.mono_set (fun _ hx => productLeaves_subset hR hx.1)

/-- Small density in the parent removes at most half of each child's
volume. Constancy of the full difference gives the paper's factor-two energy
comparison, including empty products and zero-dimensional coordinate blocks. -/
theorem productDifference_child_energy
    (Q : ∀ i, Box (Fin (d i))) (F : boundedMeasurableFunctions d)
    (E : Set (ProductPoint d)) (hE : MeasurableSet E)
    (hden : volume.real (productBox Q ∩ E) ≤
      (1 / (2 : ℝ) ^ ((∑ i, d i) + 1)) * volume.real (productBox Q)) :
    (∫ x in productBox Q, ((productDifferenceMap Finset.univ Q F).1 x) ^ 2) ≤
      2 * (∫ x in (productBox Q \ E), ((productDifferenceMap Finset.univ Q F).1 x) ^ 2) := by
  let f : ProductPoint d → ℝ := fun x => ((productDifferenceMap Finset.univ Q F).1 x) ^ 2
  have hconst : ProductLeafConstant Q (fun _ => 1) f := by
    intro R hR x hx y hy
    exact congrArg (fun t : ℝ => t ^ 2)
      (productDifference_constant_on_child Q R hR F x hx y hy)
  have hfi := integrableOn_productLeafConstant Q (fun _ => 1) f hconst
  have hroot : (∫ x in productBox Q, f x) =
      ∑ R ∈ productLeaves Q (fun _ => 1), ∫ x in productBox R, f x := by
    simpa only [Set.sdiff_empty] using
      integral_productLeaves_sdiff Q (fun _ => 1) ∅ MeasurableSet.empty f hfi
  change (∫ x in productBox Q, f x) ≤ 2 * (∫ x in (productBox Q \ E), f x)
  rw [hroot, integral_productLeaves_sdiff Q (fun _ => 1) E hE f hfi, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro R hR
  have hcorner : (fun i => (R i).upper) ∈ productBox R :=
    (mem_productBox R _).mpr (fun i => (R i).upper_mem)
  have heq : ∀ x ∈ productBox R, f x = f (fun i => (R i).upper) :=
    fun x hx => hconst R hR x hx _ hcorner
  have hfull : (∫ x in productBox R, f x) =
      volume.real (productBox R) * f (fun i => (R i).upper) := by
    calc
      _ = ∫ _ in productBox R, f (fun i => (R i).upper) :=
        setIntegral_congr_fun (measurableSet_productBox R) heq
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  have hpart : (∫ x in (productBox R \ E), f x) =
      volume.real (productBox R \ E) * f (fun i => (R i).upper) := by
    calc
      _ = ∫ _ in (productBox R \ E), f (fun i => (R i).upper) :=
        setIntegral_congr_fun ((measurableSet_productBox R).diff hE)
          (fun x hx => heq x hx.1)
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  rw [hfull, hpart]
  have hc : 0 ≤ f (fun i => (R i).upper) := sq_nonneg _
  calc
    _ ≤ (2 * volume.real (productBox R \ E)) * f (fun i => (R i).upper) :=
      mul_le_mul_of_nonneg_right (child_complement_volume Q R hR E hE hden) hc
    _ = _ := by ring

end ReyZygmund
