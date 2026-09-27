import ReyZygmund.Maximal.Product
import ReyZygmund.Projection.AveragedDenominator

/-! # The positive maximal function of a finite family

The maximum ranges over the supplied rectangles, and is zero for the empty family.
For the averaging family associated with the common projection, coverage gives
positivity. Each selected partition rectangle gives the bound for the averaged
denominator.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- The positive maximal function over exactly a finite family of rectangles. -/
noncomputable def finiteFamilyMaximal
    (G : Finset (∀ i, Box (Fin (d i)))) (F : boundedMeasurableFunctions d)
    (x : ProductPoint d) : ℝ :=
  if h : G.Nonempty then G.sup' h (fun Q =>
    (productBox Q).indicator
      (fun _ => (∫ y in productBox Q, |F.1 y|) / volume.real (productBox Q)) x)
  else 0

theorem finiteFamilyMaximal_empty (F : boundedMeasurableFunctions d) :
    finiteFamilyMaximal ∅ F = 0 := by
  funext x
  simp [finiteFamilyMaximal]

theorem finiteFamilyMaximal_nonneg
    (G : Finset (∀ i, Box (Fin (d i)))) (F : boundedMeasurableFunctions d)
    (x : ProductPoint d) : 0 ≤ finiteFamilyMaximal G F x := by
  classical
  by_cases h : G.Nonempty
  · obtain ⟨Q, hQ⟩ := h
    rw [finiteFamilyMaximal, dite_eq_left ⟨Q, hQ⟩]
    apply le_trans _ (Finset.le_sup' (fun R => (productBox R).indicator
      (fun _ => (∫ y in productBox R, |F.1 y|) / volume.real (productBox R)) x) hQ)
    exact Set.indicator_nonneg (fun _ _ =>
      div_nonneg (integral_nonneg (fun y => abs_nonneg (F.1 y))) measureReal_nonneg) x
  · simp [finiteFamilyMaximal, h]

theorem measurable_finiteFamilyMaximal
    (G : Finset (∀ i, Box (Fin (d i)))) (F : boundedMeasurableFunctions d) :
    Measurable (finiteFamilyMaximal G F) := by
  classical
  by_cases h : G.Nonempty
  · have hm := Finset.measurable_sup' (s := G) h
      (fun Q _ => (measurable_const : Measurable (fun _ : ProductPoint d =>
        (∫ y in productBox Q, |F.1 y|) / volume.real (productBox Q))).indicator
          (measurableSet_productBox Q))
    convert hm using 1
    funext x
    rw [finiteFamilyMaximal, dite_eq_left h, Finset.sup'_apply]
  · have hz : finiteFamilyMaximal G F = (fun _ => 0) := by
      funext x
      simp [finiteFamilyMaximal, h]
    rw [hz]
    exact measurable_const

/-- Every selected supported mean is bounded by this maximum. -/
theorem positiveMean_le_finiteFamilyMaximal
    (G : Finset (∀ i, Box (Fin (d i)))) (F : boundedMeasurableFunctions d)
    (Q : ∀ i, Box (Fin (d i))) (hQ : Q ∈ G) (x : ProductPoint d) :
    (productBox Q).indicator
      (fun _ => (∫ y in productBox Q, |F.1 y|) / volume.real (productBox Q)) x ≤
      finiteFamilyMaximal G F x := by
  rw [finiteFamilyMaximal, dite_eq_left ⟨Q, hQ⟩]
  exact Finset.le_sup' (fun R => (productBox R).indicator
    (fun _ => (∫ y in productBox R, |F.1 y|) / volume.real (productBox R)) x) hQ

/-- On a rectangle where the input is nonnegative, its signed product average
is itself one of the positive means in the family maximum. -/
theorem productAverageMap_le_finiteFamilyMaximal
    (G : Finset (∀ i, Box (Fin (d i)))) (F : boundedMeasurableFunctions d)
    (Q : ∀ i, Box (Fin (d i))) (hQ : Q ∈ G)
    (hpos : ∀ y ∈ productBox Q, 0 ≤ F.1 y) (x : ProductPoint d) :
    (productAverageMap Finset.univ Q F).1 x ≤ finiteFamilyMaximal G F x := by
  rw [productAverageMap_univ_eq_integral]
  have heq : (∫ y in productBox Q, F.1 y) = ∫ y in productBox Q, |F.1 y| := by
    apply setIntegral_congr_fun (measurableSet_productBox Q)
    intro y hy
    exact (abs_of_nonneg (hpos y hy)).symm
  rw [heq]
  exact positiveMean_le_finiteFamilyMaximal G F Q hQ x

/-- Restricting the family to retained descendants can only decrease the
ordinary finite rectangular maximal function. -/
theorem finiteFamilyMaximal_le_product
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) :
    finiteFamilyMaximal G F x ≤ finiteProductMaximal I N Finset.univ F x := by
  by_cases h : G.Nonempty
  · rw [finiteFamilyMaximal, dite_eq_left h, finiteProductMaximal_univ_eq_integral]
    apply Finset.sup'_le
    intro Q hQ
    exact Finset.le_sup' (fun R => (productBox R).indicator
      (fun _ => (∫ y in productBox R, |F.1 y|) / volume.real (productBox R)) x) (hG hQ)
  · simpa [finiteFamilyMaximal, h] using
      finiteProductMaximal_nonneg I N Finset.univ F x

/-- Positivity uses averaging-family coverage. A positive number of
coordinate factors is essential; no incomparability is assumed. -/
theorem averagingFamilyMaximal_pos (hm : 0 < m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (F : boundedMeasurableFunctions d) (hpos : ∀ y ∈ productBox I, 0 < F.1 y)
    (x : ProductPoint d) (hx : x ∈ productBox I) :
    0 < finiteFamilyMaximal (averagingRectangles I N G) F x := by
  obtain ⟨Q, hQ, hxQ⟩ := averagingRectangles_cover hm I N G hG x hx
  have hdesc := averagingRectangles_subset_productDescendants I N G hQ
  have hQI : ∀ i, Q i ≤ I i := fun i =>
    le_of_mem_descendants (mem_productDescendants.mp hdesc i)
  have hp := productAverageMap_pos I F hpos Finset.univ Q
    (fun i _ => hQI i) x hx (fun i _ => (mem_productBox Q x).mp hxQ i)
  apply hp.trans_le
  exact productAverageMap_le_finiteFamilyMaximal _ F Q hQ
    (fun y hy => (hpos y
      (productBox_subset_root_of_mem_productDescendants hdesc hy)).le) x

/-- The selected partition rectangle gives the paper's denominator
comparison. This does not replace it by a larger ordinary maximal function. -/
theorem averagedDenominator_le_familyMaximal
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (F : boundedMeasurableFunctions d) (hpos : ∀ y ∈ productBox I, 0 ≤ F.1 y)
    (j : Fin m) (Q : ∀ i, Box (Fin (d i)))
    (hQ : ∀ i, i ≠ j → Q i ∈ descendants (I i) (N i))
    (x : ProductPoint d) (hx : x j ∈ I j) :
    coordinateCrossAverage j (I j) (N j) (eligibleProjections j G Q)
      (productAverageMap (Finset.univ.erase j) Q F).1 x ≤
        finiteFamilyMaximal (averagingRectangles I N G) F x := by
  have he := eligibleProjections_subset_descendants I N j G Q
    (fun R hR i => mem_productDescendants.mp (hG hR) i)
  obtain ⟨P, hP, hxP⟩ := maximalPartition_isPartition (I j) (N j)
    (eligibleProjections j G Q) he (x j) hx
  rw [averagedDenominator_eq_productAverage I N G hG j Q P hP F x hxP]
  have hR := update_mem_averagingRectangles I N G hG j Q hQ P hP
  apply productAverageMap_le_finiteFamilyMaximal _ F _ hR
  intro y hy
  exact hpos y (productBox_subset_root_of_mem_productDescendants
    (averagingRectangles_subset_productDescendants I N G hR) hy)

end ReyZygmund
