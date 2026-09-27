import ReyZygmund.Geometry.ProductOrthogonality

/-! # Children of a product rectangle

Bisecting each side partitions the product rectangle. We compute the subrectangles' volumes
and prove constancy of the full product difference on each one, including the
half-open boundaries and empty-coordinate case.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem leaves_one_eq_splitCenter {k : ℕ} (Q : Box (Fin k)) :
    leaves Q 1 = (Prepartition.splitCenter Q).boxes := by
  ext R
  change R ∈ level Q (0 + 1) ↔ R ∈ Prepartition.splitCenter Q
  rw [level_succ, level_zero, Prepartition.mem_biUnion]
  constructor
  · rintro ⟨P, hP, hR⟩
    have hPQ : P = Q := Prepartition.mem_top.mp hP
    subst P
    exact hR
  · intro hR
    exact ⟨Q, Prepartition.mem_top.mpr rfl, hR⟩

private theorem product_child_mem_splitCenter
    (Q R : ∀ i, Box (Fin (d i))) (hR : R ∈ productLeaves Q (fun _ => 1)) (i : Fin m) :
    R i ∈ Prepartition.splitCenter (Q i) := by
  have hi : R i ∈ leaves (Q i) 1 := Fintype.mem_piFinset.mp hR i
  rw [leaves_one_eq_splitCenter] at hi
  exact hi

private theorem child_volume {k : ℕ} {Q R : Box (Fin k)}
    (hR : R ∈ Prepartition.splitCenter Q) :
    volume.real (R : Set (Fin k → ℝ)) =
      volume.real (Q : Set (Fin k → ℝ)) / (2 : ℝ) ^ k := by
  simp only [measureReal_def, Box.volume_apply']
  simp_rw [Prepartition.upper_sub_lower_of_mem_splitCenter hR]
  rw [Finset.prod_div_distrib]
  simp

private theorem productBox_volume_real (Q : ∀ i, Box (Fin (d i))) :
    volume.real (productBox Q) = ∏ i, volume.real (Q i : Set (Fin (d i) → ℝ)) := by
  change (Measure.pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
    (Set.pi Set.univ (fun i => (Q i : Set (Fin (d i) → ℝ))))).toReal =
      ∏ i, (volume (Q i : Set (Fin (d i) → ℝ))).toReal
  rw [Measure.pi_pi, ENNReal.toReal_prod]

/-- The exact volume of each Cartesian product child, in the measure. -/
theorem product_child_volume (Q R : ∀ i, Box (Fin (d i)))
    (hR : R ∈ productLeaves Q (fun _ => 1)) :
    volume.real (productBox R) =
      volume.real (productBox Q) / (2 : ℝ) ^ (∑ i, d i) := by
  rw [productBox_volume_real R, productBox_volume_real Q]
  have hcoord (i : Fin m) : volume.real (R i : Set (Fin (d i) → ℝ)) =
      volume.real (Q i : Set (Fin (d i) → ℝ)) / (2 : ℝ) ^ d i :=
    child_volume (product_child_mem_splitCenter Q R hR i)
  simp_rw [hcoord]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]

private theorem full_difference_child_update
    (Q R : ∀ i, Box (Fin (d i))) (hR : R ∈ productLeaves Q (fun _ => 1))
    (F : boundedMeasurableFunctions d) (i : Fin m) (x : ProductPoint d)
    (hx : x i ∈ R i) (z : Fin (d i) → ℝ) (hz : z ∈ R i) :
    (productDifferenceMap Finset.univ Q F).1 (Function.update x i z) =
      (productDifferenceMap Finset.univ Q F).1 x := by
  rw [productDifferenceMap_eq_mul_erase Finset.univ i (Finset.mem_univ i) Q]
  simp only [Module.End.mul_apply, differenceMap_apply, coordinateDifference_slice,
    Function.update_self, Function.update_idem]
  exact DifferenceAlgebra.boxDifference_constant_on_child
    (product_child_mem_splitCenter Q R hR i) _ z hz (x i) hx

private theorem constant_of_coordinate_updates
    (R : ∀ i, Box (Fin (d i))) (g : ProductPoint d → ℝ)
    (hg : ∀ (i : Fin m) (x : ProductPoint d), x ∈ productBox R →
      ∀ z ∈ R i, g (Function.update x i z) = g x) :
    ∀ x ∈ productBox R, ∀ y ∈ productBox R, g x = g y := by
  intro x hx y hy
  let z (A : Finset (Fin m)) : ProductPoint d :=
    fun i => if i ∈ A then y i else x i
  have hz (A : Finset (Fin m)) : z A ∈ productBox R := by
    apply (mem_productBox R _).mpr
    intro i
    by_cases hi : i ∈ A
    · simpa only [z, ite_eq_left hi] using (mem_productBox R y).mp hy i
    · simpa only [z, ite_eq_right hi] using (mem_productBox R x).mp hx i
  have h (A : Finset (Fin m)) : g (z A) = g x := by
    induction A using Finset.induction_on with
    | empty => simp [z]
    | @insert i A _hi ih =>
      have heq : z (insert i A) = Function.update (z A) i (y i) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp only [z, Finset.mem_insert_self, ite_true, Function.update_self]
        · simp only [z, Finset.mem_insert, hji, false_or, Function.update_of_ne hji]
      rw [heq, hg i (z A) (hz A) (y i) ((mem_productBox R y).mp hy i)]
      exact ih
  simpa only [z, Finset.mem_univ, ite_true] using (h Finset.univ).symm

/-- A full product difference is pointwise constant on every child. -/
theorem productDifference_constant_on_child
    (Q R : ∀ i, Box (Fin (d i))) (hR : R ∈ productLeaves Q (fun _ => 1))
    (F : boundedMeasurableFunctions d) :
    ∀ x ∈ productBox R, ∀ y ∈ productBox R,
      (productDifferenceMap Finset.univ Q F).1 x =
        (productDifferenceMap Finset.univ Q F).1 y := by
  apply constant_of_coordinate_updates R (productDifferenceMap Finset.univ Q F).1
  intro i x hx z hz
  exact full_difference_child_update Q R hR F i x
    ((mem_productBox R x).mp hx i) z hz

private theorem full_difference_zero_off_parent
    (Q : ∀ i, Box (Fin (d i))) (F : boundedMeasurableFunctions d)
    (x : ProductPoint d) (hx : x ∉ productBox Q) :
    (productDifferenceMap Finset.univ Q F).1 x = 0 := by
  have hnot : ¬ ∀ i, x i ∈ Q i := fun h => hx ((mem_productBox Q x).mpr h)
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  rw [productDifferenceMap_eq_mul_erase Finset.univ i (Finset.mem_univ i) Q]
  simp only [Module.End.mul_apply, differenceMap_apply, coordinateDifference_slice]
  exact DifferenceAlgebra.boxDifference_eq_zero_of_notMem (Q i) _ hi

/-- A nonzero full difference is nonzero at every point of one child. -/
theorem productDifference_exists_nonzero_child
    (Q : ∀ i, Box (Fin (d i))) (F : boundedMeasurableFunctions d)
    (hne : productDifferenceMap Finset.univ Q F ≠ 0) :
    ∃ R ∈ productLeaves Q (fun _ => 1), ∃ c : ℝ,
      c ≠ 0 ∧ ∀ x ∈ productBox R,
        (productDifferenceMap Finset.univ Q F).1 x = c := by
  have hex : ∃ x, (productDifferenceMap Finset.univ Q F).1 x ≠ 0 := by
    by_contra h
    apply hne
    apply Subtype.ext
    funext x
    change (productDifferenceMap Finset.univ Q F).1 x = 0
    by_contra hx
    exact h ⟨x, hx⟩
  obtain ⟨x, hx0⟩ := hex
  have hx : x ∈ productBox Q := by
    by_contra h
    exact hx0 (full_difference_zero_off_parent Q F x h)
  obtain ⟨R, hR, hxR⟩ := productLeaves_cover Q (fun _ => 1) x hx
  refine ⟨R, hR, (productDifferenceMap Finset.univ Q F).1 x, hx0, ?_⟩
  intro y hy
  exact productDifference_constant_on_child Q R hR F y hy x hxR

end ReyZygmund.Geometry
