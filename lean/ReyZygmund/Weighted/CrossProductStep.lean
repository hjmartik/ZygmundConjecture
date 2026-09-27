import ReyZygmund.Weighted.CrossCoordinate
import ReyZygmund.Geometry.ProductAverageProperties
import ReyZygmund.Geometry.ProductOrthogonality

/-! # Weighted cross-coordinate contraction on a cylinder

The product average is positive on the selected-cube support. Extending the weight
by one elsewhere leaves both energies unchanged: selected-cube membership is
constant along the averaging coordinate, and the numerator vanishes on other
slices. Constancy on the smallest cubes gives finite integrals.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

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

private theorem patched_weight_leaf (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (B : Finset (Fin m)) (Q : ∀ i, Box (Fin (d i)))
    (hQ : ∀ i ∈ B, Q i ∈ descendants (I i) (N i))
    (v : ProductPoint d → ℝ) (hv : ProductLeafConstant I N v) :
    ProductLeafConstant I N (fun x => if ∀ i ∈ B, x i ∈ Q i then v x else 1) := by
  intro P hP x hx y hy
  have heq : (∀ i ∈ B, x i ∈ Q i) ↔ ∀ i ∈ B, y i ∈ Q i := by
    have hi (i : Fin m) (hi : i ∈ B) : x i ∈ Q i ↔ y i ∈ Q i :=
      descendant_membership_leaf (I i) (N i) (Q i) (P i) (hQ i hi)
        (Fintype.mem_piFinset.mp hP i) (x i) (y i)
        ((mem_productBox P x).mp hx i) ((mem_productBox P y).mp hy i)
    exact ⟨fun h i hiB => (hi i hiB).mp (h i hiB),
      fun h i hiB => (hi i hiB).mpr (h i hiB)⟩
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

private theorem cross_zero_off_mixed (B : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) (j : Fin m) (hj : j ∉ B)
    (u : ProductPoint d → ℝ) (hu : ∀ x, (¬ ∀ i ∈ B, x i ∈ Q i) → u x = 0)
    (I : Box (Fin (d j))) (N : ℕ) (eligible : Finset (Box (Fin (d j))))
    (x : ProductPoint d) (hx : ¬ ∀ i ∈ B, x i ∈ Q i) :
    coordinateCrossAverage j I N eligible u x = 0 := by
  have hzero : (fun y => u (Function.update x j y)) =
      (fun _ : Fin (d j) → ℝ => (0 : ℝ)) := by
    funext y
    exact hu _ (fun h => hx ((mixed_update_iff B Q j hj x y).mp h))
  change finiteCrossAverage I N eligible (fun y => u (Function.update x j y)) (x j) = 0
  rw [hzero]
  simp [finiteCrossAverage, boxAverage]

private theorem cross_patch_eq (B : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) (j : Fin m) (hj : j ∉ B)
    (v : ProductPoint d → ℝ) (I : Box (Fin (d j))) (N : ℕ)
    (eligible : Finset (Box (Fin (d j))))
    (x : ProductPoint d) (hx : ∀ i ∈ B, x i ∈ Q i) :
    coordinateCrossAverage j I N eligible
      (fun z => if ∀ i ∈ B, z i ∈ Q i then v z else 1) x =
      coordinateCrossAverage j I N eligible v x := by
  have heq : (fun y => if ∀ i ∈ B, (Function.update x j y) i ∈ Q i
      then v (Function.update x j y) else 1) =
      (fun y => v (Function.update x j y)) := by
    funext y
    exact ite_eq_left ((mixed_update_iff B Q j hj x y).mpr hx)
  change finiteCrossAverage I N eligible
    (fun y => if ∀ i ∈ B, (Function.update x j y) i ∈ Q i
      then v (Function.update x j y) else 1) (x j) =
    finiteCrossAverage I N eligible (fun y => v (Function.update x j y)) (x j)
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

private theorem cross_patched_energy_eq (B : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) (j : Fin m) (hj : j ∉ B)
    (u v : ProductPoint d → ℝ) (p : ℝ)
    (hu : ∀ x, (¬ ∀ i ∈ B, x i ∈ Q i) → u x = 0)
    (I : Box (Fin (d j))) (N : ℕ) (eligible : Finset (Box (Fin (d j))))
    (x : ProductPoint d) :
    (coordinateCrossAverage j I N eligible u x) ^ 2 /
      Real.rpow (coordinateCrossAverage j I N eligible
        (fun z => if ∀ i ∈ B, z i ∈ Q i then v z else 1) x) (2 - p) =
    (coordinateCrossAverage j I N eligible u x) ^ 2 /
      Real.rpow (coordinateCrossAverage j I N eligible v x) (2 - p) := by
  by_cases hx : ∀ i ∈ B, x i ∈ Q i
  · rw [cross_patch_eq B Q j hj v I N eligible x hx]
  · rw [cross_zero_off_mixed B Q j hj u hu I N eligible x hx]
    simp

private theorem cross_leaf (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (g : ProductPoint d → ℝ) (hg : ProductLeafConstant I N g)
    (j : Fin m) (eligible : Finset (Box (Fin (d j))))
    (he : eligible ⊆ descendants (I j) (N j)) :
    ProductLeafConstant I N (coordinateCrossAverage j (I j) (N j) eligible g) := by
  rw [coordinateCrossAverage_eq_sum]
  apply productLeafConstant_finsetSum
  intro R hR
  exact productLeafConstant_coordinateAverage hg j R
    (partitionCubes_subset_descendants he hR)

private theorem energy_integrable (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (u v : ProductPoint d → ℝ) (hu : ProductLeafConstant I N u)
    (hv : ProductLeafConstant I N v) (p : ℝ) :
    IntegrableOn (fun x => (u x) ^ 2 / Real.rpow (v x) (2 - p)) (productBox I) volume := by
  let g := fun x => (u x) ^ 2 / Real.rpow (v x) (2 - p)
  have hg : ProductLeafConstant I N g := by
    intro P hP x hx y hy
    dsimp only [g]
    rw [hu P hP x hx y hy, hv P hP x hx y hy]
  have hvol : volume (productBox I) < ∞ := by
    change Measure.pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
      (Set.pi Set.univ (fun i => (I i : Set (Fin (d i) → ℝ)))) < ∞
    rw [Measure.pi_pi]
    exact ENNReal.prod_lt_top (fun i _ => (I i).measure_coe_lt_top volume)
  let : IsFiniteMeasure (volume.restrict (productBox I)) :=
    isFiniteMeasure_restrict.mpr hvol.ne
  obtain ⟨C, _, hC⟩ := bounded_product_localization I N g hg
  have hloc : IntegrableOn ((productBox I).indicator g) (productBox I) volume :=
    (integrable_const C).mono'
      (measurable_product_localization I N g hg).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs] using hC x))
  exact hloc.congr_fun (fun x hx => Set.indicator_of_mem hx g)
    (measurableSet_productBox I)

private theorem energy_integral_mixed (I : ∀ i, Box (Fin (d i)))
    (B : Finset (Fin m)) (Q : ∀ i, Box (Fin (d i)))
    (u v : ProductPoint d → ℝ) (p : ℝ)
    (hu : ∀ x, (¬ ∀ i ∈ B, x i ∈ Q i) → u x = 0) :
    (∫ x in productBox I, (u x) ^ 2 / Real.rpow (v x) (2 - p)) =
      ∫ x in {x ∈ productBox I | ∀ i ∈ B, x i ∈ Q i},
        (u x) ^ 2 / Real.rpow (v x) (2 - p) := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_productBox I)
    (fun _ hx => hx.1)
  intro x hx
  have hnot : ¬ ∀ i ∈ B, x i ∈ Q i := fun h => hx.2 ⟨hx.1, h⟩
  rw [hu x hnot]
  simp

private theorem cross_energy_integral_mixed (I : ∀ i, Box (Fin (d i)))
    (N : Fin m → ℕ) (B : Finset (Fin m)) (Q : ∀ i, Box (Fin (d i)))
    (j : Fin m) (hj : j ∉ B) (eligible : Finset (Box (Fin (d j))))
    (u v : ProductPoint d → ℝ) (p : ℝ)
    (hu : ∀ x, (¬ ∀ i ∈ B, x i ∈ Q i) → u x = 0) :
    (∫ x in productBox I,
      (coordinateCrossAverage j (I j) (N j) eligible u x) ^ 2 /
        Real.rpow (coordinateCrossAverage j (I j) (N j) eligible v x) (2 - p)) =
    ∫ x in {x ∈ productBox I | ∀ i ∈ B, x i ∈ Q i},
      (coordinateCrossAverage j (I j) (N j) eligible u x) ^ 2 /
        Real.rpow (coordinateCrossAverage j (I j) (N j) eligible v x) (2 - p) := by
  exact energy_integral_mixed I B Q _ _ p
    (fun x hx => cross_zero_off_mixed B Q j hj u hu (I j) (N j) eligible x hx)

/-- The coefficient-one cross contraction with the other coordinate boxes
fixed. Positivity of the product weight is derived only on its mixed support. -/
theorem weighted_cross_product_step
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productBox I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2)
    (B : Finset (Fin m)) (j : Fin m) (hj : j ∉ B)
    (Q : ∀ i, Box (Fin (d i))) (hQ : ∀ i ∈ B, Q i ∈ interior (I i) (N i))
    (eligible : Finset (Box (Fin (d j))))
    (he : eligible ⊆ descendants (I j) (N j)) :
    let F := finiteInput I N f hf
    let u := (productDifferenceMap B Q F).1
    let v := (productAverageMap B Q F).1
    (∫ x in productBox I,
      (coordinateCrossAverage j (I j) (N j) eligible u x) ^ 2 /
        Real.rpow (coordinateCrossAverage j (I j) (N j) eligible v x) (2 - p)) ≤
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
  have hXu := cross_leaf I N u hu j eligible he
  have hXv := cross_leaf I N v hv j eligible he
  have hXw := cross_leaf I N w hw j eligible he
  have hleft := energy_integrable I N _ _ hXu hXv p
  have hleftPatch := energy_integrable I N _ _ hXu hXw p
  have hright := energy_integrable I N u v hu hv p
  have hrightPatch := energy_integrable I N u w hu hw p
  calc
    (∫ x in productBox I,
        (coordinateCrossAverage j (I j) (N j) eligible u x) ^ 2 /
          Real.rpow (coordinateCrossAverage j (I j) (N j) eligible v x) (2 - p)) ≤
        ∫ x in productBox I,
          (coordinateCrossAverage j (I j) (N j) eligible u x) ^ 2 /
            Real.rpow (coordinateCrossAverage j (I j) (N j) eligible w x) (2 - p) :=
      setIntegral_mono_on hleft hleftPatch (measurableSet_productBox I)
        (fun x _ => (cross_patched_energy_eq B Q j hj u v p hus (I j) (N j) eligible x).symm.le)
    _ ≤ ∫ x in productBox I, (u x) ^ 2 / Real.rpow (w x) (2 - p) :=
      coordinateCrossAverage_weighted_square_integral I N u w hu hw hwpos j eligible he p hp hp2
    _ ≤ ∫ x in productBox I, (u x) ^ 2 / Real.rpow (v x) (2 - p) :=
      setIntegral_mono_on hrightPatch hright (measurableSet_productBox I)
        (fun x _ => (patched_energy_eq B Q u v p hus x).le)

end ReyZygmund
