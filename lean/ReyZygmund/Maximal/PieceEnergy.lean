import ReyZygmund.Geometry.ProductL2
import ReyZygmund.Geometry.FiniteSquare
import ReyZygmund.Maximal.ChildEnergy

/-! # Energy of a finite density group

Orthogonality on the top rectangle, the childwise energy estimate and support of
full differences reduce the selected sum's energy to the square function on
`B \ E`.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem piece_integrableOn_bounded_sq
    (I : ∀ i, Box (Fin (d i))) (U : boundedMeasurableFunctions d) :
    IntegrableOn (fun x => (U.1 x) ^ 2) (productRectangle I) volume := by
  let : IsFiniteMeasure (volume.restrict (productRectangle I)) :=
    isFiniteMeasure_restrict.mpr (productRectangle_volume_lt_top I).ne
  obtain ⟨C, hC, hU⟩ := U.2.2
  refine (integrable_const (C ^ 2)).mono' (U.2.1.pow_const (2 : ℕ)).aestronglyMeasurable ?_
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (U.1 x)) hC).mpr (hU x)

private theorem piece_full_difference_zero_off_parent
    (Q : ∀ i, Box (Fin (d i))) (F : boundedMeasurableFunctions d)
    (x : ProductPoint d) (hx : x ∉ productRectangle Q) :
    (productDifferenceMap Finset.univ Q F).1 x = 0 := by
  have hnot : ¬ ∀ i, x i ∈ Q i := fun h => hx ((mem_productRectangle Q x).mpr h)
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  rw [productDifferenceMap_eq_mul_erase Finset.univ i (Finset.mem_univ i) Q]
  simp only [Module.End.mul_apply, differenceMap_apply, coordinateDifference_slice]
  exact DifferenceAlgebra.boxDifference_eq_zero_of_notMem (Q i) _ hi

private theorem piece_difference_integral_parent
    (Q : ∀ i, Box (Fin (d i))) (F : boundedMeasurableFunctions d)
    (S : Set (ProductPoint d)) (hS : MeasurableSet S) (hQS : productRectangle Q ⊆ S) :
    (∫ x in S, ((productDifferenceMap Finset.univ Q F).1 x) ^ 2) =
      ∫ x in productRectangle Q, ((productDifferenceMap Finset.univ Q F).1 x) ^ 2 := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hS hQS
  intro x hx
  rw [piece_full_difference_zero_off_parent Q F x hx.2]
  norm_num

private theorem piece_difference_integral_sdiff
    (Q : ∀ i, Box (Fin (d i))) (F : boundedMeasurableFunctions d)
    (E B : Set (ProductPoint d)) (hE : MeasurableSet E) (hB : MeasurableSet B)
    (hQB : productRectangle Q ⊆ B) :
    (∫ x in (productRectangle Q \ E), ((productDifferenceMap Finset.univ Q F).1 x) ^ 2) =
      ∫ x in (B \ E), ((productDifferenceMap Finset.univ Q F).1 x) ^ 2 := by
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hB.diff hE)
    (fun _ hx => ⟨hQB hx.1, hx.2⟩)
  intro x hx
  have hxQ : x ∉ productRectangle Q := fun h => hx.2 ⟨h, hx.1.2⟩
  rw [piece_full_difference_zero_off_parent Q F x hxQ]
  norm_num

private theorem piece_sum_sq_le_square
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (H : Finset (∀ i, Box (Fin (d i))))
    (hH : H ⊆ Projection.productInterior I N) (x : ProductPoint d) :
    (∑ Q ∈ H, ((productDifferenceMap Finset.univ Q F).1 x) ^ 2) ≤
      (finiteSquareFunction I N Finset.univ F x) ^ 2 := by
  have hindices : partialInterior I N Finset.univ = Projection.productInterior I N := by
    simp only [partialInterior, Projection.productInterior, Finset.mem_univ, ite_true]
  rw [finiteSquareFunction_sq, hindices]
  exact Finset.sum_le_sum_of_subset_of_nonneg hH (fun _ _ _ => sq_nonneg _)

/-- The energy estimate for a finite density group uses a square-function bound
on `B \ E`. -/
theorem finite_piece_energy
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (F : boundedMeasurableFunctions d) (H : Finset (∀ i, Box (Fin (d i))))
    (hH : H ⊆ Projection.productInterior I N)
    (E B : Set (ProductPoint d)) (hE : MeasurableSet E) (hB : MeasurableSet B)
    (hBI : B ⊆ productRectangle I) (hcover : ∀ Q ∈ H, productRectangle Q ⊆ B)
    (hden : ∀ Q ∈ H, volume.real (productRectangle Q ∩ E) ≤
      (1 / (2 : ℝ) ^ ((∑ i, d i) + 1)) * volume.real (productRectangle Q))
    (T : ℝ) (hT : 0 ≤ T)
    (hbound : ∀ x ∈ B \ E, finiteSquareFunction I N Finset.univ F x ≤ T) :
    (∫ x in productRectangle I, (∑ Q ∈ H, (productDifferenceMap Finset.univ Q F).1 x) ^ 2) ≤
      2 * T ^ 2 * volume.real B := by
  have hBfin : volume B ≠ ∞ :=
    measure_ne_top_of_subset hBI (productRectangle_volume_lt_top I).ne
  have hBEfin : volume (B \ E) ≠ ∞ :=
    measure_ne_top_of_subset Set.sdiff_subset hBfin
  have hQI (Q : ∀ i, Box (Fin (d i))) :
      IntegrableOn (fun x => ((productDifferenceMap Finset.univ Q F).1 x) ^ 2)
        (B \ E) volume :=
    (piece_integrableOn_bounded_sq I (productDifferenceMap Finset.univ Q F)).mono_set
      (fun _ hx => hBI hx.1)
  have hsumI : IntegrableOn
      (fun x => ∑ Q ∈ H, ((productDifferenceMap Finset.univ Q F).1 x) ^ 2)
      (B \ E) volume :=
    integrable_finsetSum H (fun Q _ => hQI Q)
  have hlocal : (∫ x in (B \ E), ∑ Q ∈ H,
      ((productDifferenceMap Finset.univ Q F).1 x) ^ 2) ≤ T ^ 2 * volume.real B := by
    calc
      _ ≤ ∫ _ in (B \ E), T ^ 2 := by
        apply setIntegral_mono_on hsumI (integrableOn_const hBEfin) (hB.diff hE)
        intro x hx
        exact (piece_sum_sq_le_square I N F H hH x).trans
          ((sq_le_sq₀ (Real.sqrt_nonneg _) hT).mpr (hbound x hx))
      _ = volume.real (B \ E) * T ^ 2 := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ volume.real B * T ^ 2 :=
        mul_le_mul_of_nonneg_right (measureReal_mono Set.sdiff_subset hBfin) (sq_nonneg T)
      _ = _ := mul_comm _ _
  calc
    _ = ∑ Q ∈ H, ∫ x in productRectangle I, ((productDifferenceMap Finset.univ Q F).1 x) ^ 2 :=
      productDifference_integral_sum_sq I N hd F H hH
    _ = ∑ Q ∈ H, ∫ x in productRectangle Q, ((productDifferenceMap Finset.univ Q F).1 x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro Q hQ
      exact piece_difference_integral_parent Q F (productRectangle I) (measurableSet_productRectangle I)
        ((hcover Q hQ).trans hBI)
    _ ≤ ∑ Q ∈ H, 2 * (∫ x in (productRectangle Q \ E),
        ((productDifferenceMap Finset.univ Q F).1 x) ^ 2) := by
      apply Finset.sum_le_sum
      intro Q hQ
      exact productDifference_child_energy Q F E hE (hden Q hQ)
    _ = ∑ Q ∈ H, 2 * (∫ x in (B \ E),
        ((productDifferenceMap Finset.univ Q F).1 x) ^ 2) := by
      apply Finset.sum_congr rfl
      intro Q hQ
      rw [piece_difference_integral_sdiff Q F E B hE hB (hcover Q hQ)]
    _ = 2 * (∑ Q ∈ H, ∫ x in (B \ E),
        ((productDifferenceMap Finset.univ Q F).1 x) ^ 2) := (Finset.mul_sum _ _ _).symm
    _ = 2 * (∫ x in (B \ E), ∑ Q ∈ H,
        ((productDifferenceMap Finset.univ Q F).1 x) ^ 2) := by
      rw [integral_finsetSum H (fun Q _ => hQI Q)]
    _ ≤ 2 * (T ^ 2 * volume.real B) :=
      mul_le_mul_of_nonneg_left hlocal (by norm_num : (0 : ℝ) ≤ 2)
    _ = 2 * T ^ 2 * volume.real B := by ring

end ReyZygmund
