import ReyZygmund.Weighted.Coordinate
import ReyZygmund.Geometry.ProductAverageProperties
import ReyZygmund.Geometry.ProductOrthogonality

/-! # A weighted recurrence with other coordinate cubes fixed

The product average is positive on its support region, which may be smaller than
the top rectangle. Extend the weight positively outside that region to apply the
coordinate estimate. Both energy integrals remain unchanged.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem mixed_update_iff (B : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) (j : Fin m) (hj : j ∉ B)
    (x : ProductPoint d) (y : Fin (d j) → ℝ) :
    (∀ i ∈ B, (Function.update x j y) i ∈ Q i) ↔ ∀ i ∈ B, x i ∈ Q i := by
  have hij (i : Fin m) (hi : i ∈ B) : i ≠ j := by
    intro h
    subst i
    exact hj hi
  constructor
  · intro h i hi
    simpa only [Function.update_of_ne (hij i hi)] using h i hi
  · intro h i hi
    simpa only [Function.update_of_ne (hij i hi)] using h i hi

private theorem descendant_membership_leaf {k : ℕ} (I : Box (Fin k)) (N : ℕ)
    (Q P : Box (Fin k)) (hQ : Q ∈ descendants I N) (hP : P ∈ leaves I N)
    (x y : Fin k → ℝ) (hx : x ∈ P) (hy : y ∈ P) : x ∈ Q ↔ y ∈ Q := by
  obtain ⟨n, hn, hQn⟩ := mem_descendants.mp hQ
  rcases level_le_or_disjoint hn hP hQn with hPQ | hdis
  · exact ⟨fun _ => hPQ hy, fun _ => hPQ hx⟩
  · exact ⟨fun hxQ => (Set.disjoint_left.mp hdis hx hxQ).elim,
      fun hyQ => (Set.disjoint_left.mp hdis hy hyQ).elim⟩

private theorem mixed_membership_leaf (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (B : Finset (Fin m)) (Q : ∀ i, Box (Fin (d i)))
    (hQ : ∀ i ∈ B, Q i ∈ descendants (I i) (N i))
    (P : ∀ i, Box (Fin (d i))) (hP : P ∈ productLeaves I N)
    (x y : ProductPoint d) (hx : x ∈ productBox P) (hy : y ∈ productBox P) :
    (∀ i ∈ B, x i ∈ Q i) ↔ ∀ i ∈ B, y i ∈ Q i := by
  have heq (i : Fin m) (hi : i ∈ B) : x i ∈ Q i ↔ y i ∈ Q i :=
    descendant_membership_leaf (I i) (N i) (Q i) (P i) (hQ i hi)
      (Fintype.mem_piFinset.mp hP i) (x i) (y i)
      ((mem_productBox P x).mp hx i) ((mem_productBox P y).mp hy i)
  exact ⟨fun h i hi => (heq i hi).mp (h i hi),
    fun h i hi => (heq i hi).mpr (h i hi)⟩

private theorem patched_weight_leaf (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (B : Finset (Fin m)) (Q : ∀ i, Box (Fin (d i)))
    (hQ : ∀ i ∈ B, Q i ∈ descendants (I i) (N i))
    (v : ProductPoint d → ℝ) (hv : ProductLeafConstant I N v) :
    ProductLeafConstant I N (fun x => if ∀ i ∈ B, x i ∈ Q i then v x else 1) := by
  intro P hP x hx y hy
  have heq := mixed_membership_leaf I N B Q hQ P hP x y hx hy
  change (if ∀ i ∈ B, x i ∈ Q i then v x else 1) =
    (if ∀ i ∈ B, y i ∈ Q i then v y else 1)
  by_cases hmem : ∀ i ∈ B, x i ∈ Q i
  · rw [ite_eq_left hmem, ite_eq_left (heq.mp hmem)]
    exact hv P hP x hx y hy
  · rw [ite_eq_right hmem, ite_eq_right (fun h => hmem (heq.mpr h))]

private theorem productDifference_zero_off_mixed (B : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) (F : boundedMeasurableFunctions d)
    (x : ProductPoint d) (hx : ¬ ∀ i ∈ B, x i ∈ Q i) :
    (productDifferenceMap B Q F).1 x = 0 := by
  push Not at hx
  obtain ⟨i, hi, hxi⟩ := hx
  rw [productDifferenceMap_eq_mul_erase B i hi Q]
  simp only [Module.End.mul_apply, differenceMap_apply, coordinateDifference_slice]
  exact DifferenceAlgebra.boxDifference_eq_zero_of_notMem (Q i) _ hxi

private theorem coordinateDifference_zero_off_mixed (B : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) (j : Fin m) (hj : j ∉ B)
    (u : ProductPoint d → ℝ) (hu : ∀ x, (¬ ∀ i ∈ B, x i ∈ Q i) → u x = 0)
    (R : Box (Fin (d j))) (x : ProductPoint d) (hx : ¬ ∀ i ∈ B, x i ∈ Q i) :
    coordinateDifference j R u x = 0 := by
  have hzero : (fun y => u (Function.update x j y)) =
      (fun _ : Fin (d j) → ℝ => (0 : ℝ)) := by
    funext y
    exact hu _ (fun h => hx ((mixed_update_iff B Q j hj x y).mp h))
  rw [coordinateDifference_slice, hzero]
  simp [boxDifference, boxAverage]

private theorem coordinateAverage_patch_eq (B : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) (j : Fin m) (hj : j ∉ B)
    (v : ProductPoint d → ℝ) (R : Box (Fin (d j)))
    (x : ProductPoint d) (hx : ∀ i ∈ B, x i ∈ Q i) :
    coordinateAverage j R (fun z => if ∀ i ∈ B, z i ∈ Q i then v z else 1) x =
      coordinateAverage j R v x := by
  have heq : (fun y => if ∀ i ∈ B, (Function.update x j y) i ∈ Q i
      then v (Function.update x j y) else 1) =
      (fun y => v (Function.update x j y)) := by
    funext y
    exact ite_eq_left ((mixed_update_iff B Q j hj x y).mpr hx)
  change boxAverage R
    (fun y => if ∀ i ∈ B, (Function.update x j y) i ∈ Q i
      then v (Function.update x j y) else 1) (x j) =
    boxAverage R (fun y => v (Function.update x j y)) (x j)
  rw [heq]

private theorem patched_energy_eq (B : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) (u v : ProductPoint d → ℝ) (p : ℝ)
    (hu : ∀ x, (¬ ∀ i ∈ B, x i ∈ Q i) → u x = 0) (x : ProductPoint d) :
    (u x) ^ 2 / Real.rpow (if ∀ i ∈ B, x i ∈ Q i then v x else 1) (2 - p) =
      (u x) ^ 2 / Real.rpow (v x) (2 - p) := by
  by_cases hx : ∀ i ∈ B, x i ∈ Q i
  · rw [ite_eq_left hx]
  · rw [hu x hx]
    simp

private theorem coordinate_patched_energy_eq (B : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) (j : Fin m) (hj : j ∉ B)
    (u v : ProductPoint d → ℝ) (p : ℝ)
    (hu : ∀ x, (¬ ∀ i ∈ B, x i ∈ Q i) → u x = 0)
    (R : Box (Fin (d j))) (x : ProductPoint d) :
    (coordinateDifference j R u x) ^ 2 /
      Real.rpow (coordinateAverage j R
        (fun z => if ∀ i ∈ B, z i ∈ Q i then v z else 1) x) (2 - p) =
    (coordinateDifference j R u x) ^ 2 /
      Real.rpow (coordinateAverage j R v x) (2 - p) := by
  by_cases hx : ∀ i ∈ B, x i ∈ Q i
  · rw [coordinateAverage_patch_eq B Q j hj v R x hx]
  · rw [coordinateDifference_zero_off_mixed B Q j hj u hu R x hx]
    simp

private theorem coordinate_energy_integral_mixed
    (I : ∀ i, Box (Fin (d i))) (B : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) (j : Fin m) (hj : j ∉ B)
    (u v : ProductPoint d → ℝ) (p : ℝ)
    (hu : ∀ x, (¬ ∀ i ∈ B, x i ∈ Q i) → u x = 0)
    (R : Box (Fin (d j))) :
    (∫ x in productBox I, (coordinateDifference j R u x) ^ 2 /
      Real.rpow (coordinateAverage j R v x) (2 - p)) =
    ∫ x in {x ∈ productBox I | (∀ i ∈ B, x i ∈ Q i) ∧ x j ∈ R},
      (coordinateDifference j R u x) ^ 2 /
        Real.rpow (coordinateAverage j R v x) (2 - p) := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_productBox I)
    (fun _ hx => hx.1)
  intro x hx
  have hzero : coordinateDifference j R u x = 0 := by
    by_cases hmem : ∀ i ∈ B, x i ∈ Q i
    · have hxR : x j ∉ R := fun hxR => hx.2 ⟨hx.1, hmem, hxR⟩
      rw [coordinateDifference_slice]
      exact DifferenceAlgebra.boxDifference_eq_zero_of_notMem R _ hxR
    · exact coordinateDifference_zero_off_mixed B Q j hj u hu R x hmem
  simp only [hzero, zero_pow (by decide : 2 ≠ 0), zero_div]

/-- The fixed-other-box recurrence in the product square estimate. Positivity
of the product average is derived only on its mixed support. -/
theorem weighted_product_step
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productBox I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) (B : Finset (Fin m))
    (j : Fin m) (hj : j ∉ B) (hd : 0 < d j)
    (Q : ∀ i, Box (Fin (d i))) (hQ : ∀ i ∈ B, Q i ∈ interior (I i) (N i)) :
    let F := finiteInput I N f hf
    let u := (productDifferenceMap B Q F).1
    let v := (productAverageMap B Q F).1
    (∑ R ∈ interior (I j) (N j), ∫ x in productBox I,
      (coordinateDifference j R u x) ^ 2 / Real.rpow (coordinateAverage j R v x) (2 - p)) ≤
      Real.rpow 2 ((d j : ℝ) * (2 - p)) * ((3 - p) / (p - 1)) *
        ∫ x in productBox I, (u x) ^ 2 / Real.rpow (v x) (2 - p) := by
  let F := finiteInput I N f hf
  let u := (productDifferenceMap B Q F).1
  let v := (productAverageMap B Q F).1
  let w : ProductPoint d → ℝ := fun x => if ∀ i ∈ B, x i ∈ Q i then v x else 1
  have hF : ProductLeafConstant I N F.1 := productLeafConstant_indicator hf
  have hFs : ∀ x, x ∉ productBox I → F.1 x = 0 :=
    fun x hx => Set.indicator_of_notMem hx f
  have hQd : ∀ i ∈ B, Q i ∈ descendants (I i) (N i) :=
    fun i hi => interior_subset_descendants (I i) (N i) (hQ i hi)
  have hu : ProductLeafConstant I N u :=
    (productDifferenceMap_productStep_closure I N F hF hFs B Q hQ).1
  have hv : ProductLeafConstant I N v :=
    (productAverageMap_productStep_closure I N F hF hFs B Q hQd).1
  have hw : ProductLeafConstant I N w := patched_weight_leaf I N B Q hQd v hv
  have hFpos : ∀ x ∈ productBox I, 0 < F.1 x := by
    intro x hx
    change 0 < (productBox I).indicator f x
    rw [Set.indicator_of_mem hx]
    exact hfpos x hx
  have hwpos : ∀ x ∈ productBox I, 0 < w x := by
    intro x hx
    by_cases hxQ : ∀ i ∈ B, x i ∈ Q i
    · change 0 < if ∀ i ∈ B, x i ∈ Q i then v x else 1
      rw [ite_eq_left hxQ]
      exact productAverageMap_pos I F hFpos B Q
        (fun i hi => le_of_mem_descendants (hQd i hi)) x hx hxQ
    · simp only [w, ite_eq_right hxQ, zero_lt_one]
  have hus : ∀ x, (¬ ∀ i ∈ B, x i ∈ Q i) → u x = 0 :=
    productDifference_zero_off_mixed B Q F
  have h := coordinate_weighted_square I N j hd u w p hp hp2 hu hw hwpos
  have hleft :
      (∑ R ∈ interior (I j) (N j), ∫ x in productBox I,
        (coordinateDifference j R u x) ^ 2 / Real.rpow (coordinateAverage j R w x) (2 - p)) =
      ∑ R ∈ interior (I j) (N j), ∫ x in productBox I,
        (coordinateDifference j R u x) ^ 2 / Real.rpow (coordinateAverage j R v x) (2 - p) := by
    apply Finset.sum_congr rfl
    intro R _
    apply setIntegral_congr_fun (measurableSet_productBox I)
    intro x _
    exact coordinate_patched_energy_eq B Q j hj u v p hus R x
  have hright : (∫ x in productBox I, (u x) ^ 2 / Real.rpow (w x) (2 - p)) =
      ∫ x in productBox I, (u x) ^ 2 / Real.rpow (v x) (2 - p) := by
    apply setIntegral_congr_fun (measurableSet_productBox I)
    intro x _
    exact patched_energy_eq B Q u v p hus x
  rw [hleft, hright] at h
  exact h

end ReyZygmund
