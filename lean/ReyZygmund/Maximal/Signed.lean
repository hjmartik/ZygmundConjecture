import ReyZygmund.Maximal.FamilyProperties
import ReyZygmund.Geometry.AverageDifferenceMaps

/-!
# The finite signed product maximal function

The absolute value is taken after the signed average. This distinction is
essential for the cancellation and support argument in the maximal–square
estimate. The larger positive maximal function is used only for domination.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- The maximum of absolute signed averages over product descendants. -/
noncomputable def finiteSignedProductMaximal
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) : ℝ :=
  (productDescendants I N).sup' ⟨I, root_mem_productDescendants I N⟩
    (fun Q => |(productAverageMap Finset.univ Q F).1 x|)

theorem finiteSignedProductMaximal_nonneg
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) :
    0 ≤ finiteSignedProductMaximal I N F x :=
  (abs_nonneg _).trans (Finset.le_sup'
    (fun Q => |(productAverageMap Finset.univ Q F).1 x|)
    (root_mem_productDescendants I N))

theorem measurable_finiteSignedProductMaximal
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) :
    Measurable (finiteSignedProductMaximal I N F) := by
  have h := Finset.measurable_sup' (s := productDescendants I N)
    ⟨I, root_mem_productDescendants I N⟩
    (fun Q _ => (productAverageMap Finset.univ Q F).2.1.norm)
  convert h using 1
  funext x
  simp only [finiteSignedProductMaximal, Real.norm_eq_abs]
  exact (Finset.sup'_apply (C := fun _ : ProductPoint d => ℝ)
    ⟨I, root_mem_productDescendants I N⟩
    (fun Q y => |(productAverageMap Finset.univ Q F).1 y|) x).symm

/-- Taking absolute values before integration gives the ordinary positive maximum. -/
theorem finiteSignedProductMaximal_le_positive
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) :
    finiteSignedProductMaximal I N F x ≤
      finiteFamilyMaximal (productDescendants I N) F x := by
  apply Finset.sup'_le
  intro Q hQ
  apply le_trans _ (positiveMean_le_finiteFamilyMaximal _ F Q hQ x)
  rw [productAverageMap_univ_eq_integral]
  by_cases hx : x ∈ productBox Q
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, abs_div,
      abs_of_nonneg (measureReal_nonneg : 0 ≤ volume.real (productBox Q))]
    exact div_le_div_of_nonneg_right abs_integral_le_integral_abs measureReal_nonneg
  · simp only [Set.indicator_of_notMem hx, abs_zero, le_refl]

theorem productLeafConstant_finiteSignedProductMaximal
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) :
    ProductLeafConstant I N (finiteSignedProductMaximal I N F) := by
  intro P hP x hx y hy
  apply Finset.sup'_congr _ rfl
  intro Q hQ
  have hc := (productAverageMap_productStep_closure I N F hf hs Finset.univ Q
    (fun i _ => mem_productDescendants.mp hQ i)).1
  exact congrArg abs (hc P hP x hx y hy)

/-- A full difference has no signed averages outside its parent rectangle.
This is the finite source cancellation argument, not a support assertion for
the positive maximal function. -/
theorem full_difference_average_eq_zero_off_parent
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (Q R : ∀ i, Box (Fin (d i)))
    (hQ : Q ∈ productDescendants I N) (hR : R ∈ productDescendants I N)
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) (hx : x ∉ productBox Q) :
    (productAverageMap Finset.univ R (productDifferenceMap Finset.univ Q F)).1 x = 0 := by
  by_cases hstrict : ∀ i, R i < Q i
  · have hxR : x ∉ productBox R := by
      intro h
      apply hx
      apply (mem_productBox Q x).mpr
      intro i
      exact (hstrict i).le ((mem_productBox R x).mp h i)
    rw [productAverageMap_univ_eq_integral, Set.indicator_of_notMem hxR]
  · have hbad : ∃ i ∈ (Finset.univ : Finset (Fin m)), 0 < d i ∧ ¬ R i < Q i := by
      push Not at hstrict
      obtain ⟨i, hi⟩ := hstrict
      exact ⟨i, Finset.mem_univ i, hd i, hi⟩
    have hz := productAverageMap_mul_full_difference_eq_zero I N Finset.univ R Q
      (fun i _ => mem_productDescendants.mp hR i)
      (mem_productDescendants.mp hQ) hbad
    have ha := congrArg (fun T : Module.End ℝ (boundedMeasurableFunctions d) => (T F).1 x) hz
    simpa only [Module.End.mul_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero,
      Pi.zero_apply] using ha

/-- A finite sum of full differences has signed maximal support inside the
union of its parent rectangles, or any larger set. -/
theorem finiteSignedProductMaximal_sum_eq_zero_off
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (H : Finset (∀ i, Box (Fin (d i)))) (hH : H ⊆ productDescendants I N)
    (F : boundedMeasurableFunctions d) (E : Set (ProductPoint d))
    (hE : ∀ Q ∈ H, productBox Q ⊆ E) (x : ProductPoint d) (hx : x ∉ E) :
    finiteSignedProductMaximal I N (∑ Q ∈ H, productDifferenceMap Finset.univ Q F) x = 0 := by
  apply Finset.sup'_eq_of_forall
  intro R hR
  have hz : ∀ Q ∈ H,
      (productAverageMap Finset.univ R (productDifferenceMap Finset.univ Q F)).1 x = 0 := by
    intro Q hQ
    exact full_difference_average_eq_zero_off_parent I N hd Q R (hH hQ) hR F x
      (fun hxQ => hx (hE Q hQ hxQ))
  simp only [map_sum]
  simp only [Submodule.coe_sum, Finset.sum_apply]
  rw [Finset.sum_eq_zero hz, abs_zero]

end ReyZygmund
