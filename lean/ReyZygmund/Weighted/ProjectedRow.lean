import ReyZygmund.Weighted.CrossProductStep
import ReyZygmund.Maximal.FamilyProperties
import ReyZygmund.Projection.Properties

/-!
# One row of the projected weighted square estimate

The denominator is the positive maximal function of the averaging
family. Its comparison with the cross-averaged weight is used only on the
support cylinder, where that weight is positive. Elsewhere the numerator
vanishes. No global positivity of a partially averaged weight is assumed.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

private theorem difference_zero_off_selected (A : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) (F : boundedMeasurableFunctions d)
    (x : ProductPoint d) (hx : ¬ ∀ i ∈ A, x i ∈ Q i) :
    (productDifferenceMap A Q F).1 x = 0 := by
  push Not at hx
  obtain ⟨i, hi, hxi⟩ := hx
  rw [productDifferenceMap_eq_mul_erase A i hi Q]
  simp only [Module.End.mul_apply, differenceMap_apply, coordinateDifference_slice]
  exact DifferenceAlgebra.boxDifference_eq_zero_of_notMem (Q i) _ hxi

private theorem averagedDenominator_pos_on_selected
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (F : boundedMeasurableFunctions d) (hpos : ∀ y ∈ productBox I, 0 < F.1 y)
    (j : Fin m) (Q : ∀ i, Box (Fin (d i)))
    (hQ : ∀ i, i ≠ j → Q i ∈ descendants (I i) (N i))
    (x : ProductPoint d) (hx : x ∈ productBox I)
    (hxQ : ∀ i ∈ Finset.univ.erase j, x i ∈ Q i) :
    0 < coordinateCrossAverage j (I j) (N j) (eligibleProjections j G Q)
      (productAverageMap (Finset.univ.erase j) Q F).1 x := by
  have he := eligibleProjections_subset_descendants I N j G Q
    (fun R hR i => mem_productDescendants.mp (hG hR) i)
  obtain ⟨P, hP, hxP⟩ := maximalPartition_isPartition (I j) (N j)
    (eligibleProjections j G Q) he (x j) ((mem_productBox I x).mp hx j)
  rw [averagedDenominator_eq_productAverage I N G hG j Q P hP F x hxP]
  have hR := update_mem_averagingRectangles I N G hG j Q hQ P hP
  have hdesc := averagingRectangles_subset_productDescendants I N G hR
  apply productAverageMap_pos I F hpos Finset.univ (Function.update Q j P)
    (fun i _ => le_of_mem_descendants (mem_productDescendants.mp hdesc i)) x hx
  intro i _
  by_cases hij : i = j
  · subst i
    simpa using hxP
  · simpa [hij] using hxQ i (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)

/-- The exact fixed-coordinate energy transfer with the maximal denominator. -/
theorem projected_row_energy
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productBox I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2)
    (j : Fin m) (Q : ∀ i, Box (Fin (d i)))
    (hQ : ∀ i, i ≠ j → Q i ∈ interior (I i) (N i)) :
    let F := finiteInput I N f hf
    let A := Finset.univ.erase j
    (∫ x in productBox I,
      ((productDifferenceMap A Q (finiteProjectionMap I N G F)).1 x) ^ 2 /
        Real.rpow (finiteFamilyMaximal (averagingRectangles I N G) F x) (2 - p)) ≤
      ∫ x in productBox I,
        ((productDifferenceMap A Q F).1 x) ^ 2 /
          Real.rpow ((productAverageMap A Q F).1 x) (2 - p) := by
  let F := finiteInput I N f hf
  let A := Finset.univ.erase j
  let u := (productDifferenceMap A Q F).1
  let v := (productAverageMap A Q F).1
  let Xu := coordinateCrossAverage j (I j) (N j) (eligibleProjections j G Q) u
  let Xv := coordinateCrossAverage j (I j) (N j) (eligibleProjections j G Q) v
  let M := finiteFamilyMaximal (averagingRectangles I N G) F
  have hF : ProductLeafConstant I N F.1 := productLeafConstant_indicator hf
  have hFs : ∀ x, x ∉ productBox I → F.1 x = 0 :=
    fun x hx => Set.indicator_of_notMem hx f
  have hFpos : ∀ x ∈ productBox I, 0 < F.1 x := by
    intro x hx
    change 0 < (productBox I).indicator f x
    rw [Set.indicator_of_mem hx]
    exact hfpos x hx
  have hQd : ∀ i, i ≠ j → Q i ∈ descendants (I i) (N i) :=
    fun i hij => interior_subset_descendants (I i) (N i) (hQ i hij)
  have he := eligibleProjections_subset_descendants I N j G Q
    (fun R hR i => mem_productDescendants.mp (hG hR) i)
  have hu := productDifferenceMap_productStep_closure I N F hF hFs A Q
    (fun i hi => hQ i (Finset.mem_erase.mp hi).1)
  have hv := productAverageMap_productStep_closure I N F hF hFs A Q
    (fun i hi => hQd i (Finset.mem_erase.mp hi).1)
  have hXu := (coordinateCrossAverage_productStep_closure I N u hu.1 hu.2 j
    (eligibleProjections j G Q) he).1
  have hXv := (coordinateCrossAverage_productStep_closure I N v hv.1 hv.2 j
    (eligibleProjections j G Q) he).1
  have hM := productLeafConstant_finiteFamilyMaximal I N (averagingRectangles I N G)
    (averagingRectangles_subset_productDescendants I N G) F
  change ProductLeafConstant I N Xu at hXu
  change ProductLeafConstant I N Xv at hXv
  change ProductLeafConstant I N M at hM
  have hleft : IntegrableOn (fun x => (Xu x) ^ 2 / Real.rpow (M x) (2 - p))
      (productBox I) volume := by
    apply integrableOn_productLeafConstant I N
    intro P hP x hx y hy
    dsimp only
    rw [hXu P hP x hx y hy, hM P hP x hx y hy]
  have hmiddle : IntegrableOn (fun x => (Xu x) ^ 2 / Real.rpow (Xv x) (2 - p))
      (productBox I) volume := by
    apply integrableOn_productLeafConstant I N
    intro P hP x hx y hy
    dsimp only
    rw [hXu P hP x hx y hy, hXv P hP x hx y hy]
  have hcross : (productDifferenceMap A Q (finiteProjectionMap I N G F)).1 = Xu :=
    finite_cross_projection I N hd G (fun R hR i => mem_productDescendants.mp (hG hR) i)
      f hf j Q hQ
  change (∫ x in productBox I,
      ((productDifferenceMap A Q (finiteProjectionMap I N G F)).1 x) ^ 2 /
        Real.rpow (M x) (2 - p)) ≤ ∫ x in productBox I, (u x) ^ 2 / Real.rpow (v x) (2 - p)
  rw [hcross]
  calc
    (∫ x in productBox I, (Xu x) ^ 2 / Real.rpow (M x) (2 - p)) ≤
        ∫ x in productBox I, (Xu x) ^ 2 / Real.rpow (Xv x) (2 - p) := by
      apply setIntegral_mono_on hleft hmiddle (measurableSet_productBox I)
      intro x hx
      by_cases hxQ : ∀ i ∈ A, x i ∈ Q i
      · have hpos : 0 < Xv x := averagedDenominator_pos_on_selected I N G hG F hFpos
          j Q hQd x hx hxQ
        have hbound : Xv x ≤ M x := averagedDenominator_le_familyMaximal I N G hG F
          (fun y hy => (hFpos y hy).le) j Q hQd x ((mem_productBox I x).mp hx j)
        exact div_le_div_of_nonneg_left (sq_nonneg _)
          (Real.rpow_pos_of_pos hpos _) (Real.rpow_le_rpow hpos.le hbound (by linarith))
      · have hz : Xu x = 0 := by
          rw [← hcross]
          exact difference_zero_off_selected A Q _ x hxQ
        rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, zero_div]
    _ ≤ _ := weighted_cross_product_step I N f hf hfpos p hp hp2 A j (by simp [A]) Q
      (fun i hi => hQ i (Finset.mem_erase.mp hi).1) (eligibleProjections j G Q) he

end ReyZygmund
