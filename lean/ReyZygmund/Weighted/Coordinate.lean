import ReyZygmund.Geometry.ProductIntegration
import ReyZygmund.Geometry.ProductClosure
import ReyZygmund.Geometry.ProductPartitions
import ReyZygmund.Geometry.FiniteDifferenceAlgebra
import ReyZygmund.Weighted.OneCoordinate

/-! # The weighted square estimate in one product coordinate

Lift the one-coordinate estimate to integrals over the top rectangle. The input
conditions are imposed only there. This estimate is iterated in `Product.lean` to
obtain the product square-function inequality.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem update_mem_root (I : ∀ i, Box (Fin (d i)))
    {x : ProductPoint d} (hx : x ∈ productBox I) (j : Fin m)
    {y : Fin (d j) → ℝ} (hy : y ∈ I j) :
    Function.update x j y ∈ productBox I := by
  apply (mem_productBox I _).mpr
  intro i
  by_cases hij : i = j
  · subst i
    simpa using hy
  · simpa [hij] using (mem_productBox I x).mp hx i

private theorem product_leaf_slice (I : ∀ i, Box (Fin (d i)))
    (N : Fin m → ℕ) (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (j : Fin m) {x : ProductPoint d} (hx : x ∈ productBox I) :
    ∀ Q ∈ leaves (I j) (N j), ∀ y ∈ Q, ∀ z ∈ Q,
      f (Function.update x j y) = f (Function.update x j z) := by
  intro Q hQ y hy z hz
  have hyI := (level (I j) (N j)).le_of_mem hQ hy
  have hzI := (level (I j) (N j)).le_of_mem hQ hz
  have h := productStep_coordinate_leafConstant I N f hf j x Q hQ y hy z hz
  simpa only [Set.indicator_of_mem (update_mem_root I hx j hyI),
    Set.indicator_of_mem (update_mem_root I hx j hzI)] using h

private theorem coordinateDifference_zero_off_parent (j : Fin m)
    (Q : Box (Fin (d j))) (f : ProductPoint d → ℝ) (x : ProductPoint d)
    (hx : x j ∉ Q) : coordinateDifference j Q f x = 0 := by
  rw [coordinateDifference_slice]
  exact DifferenceAlgebra.boxDifference_eq_zero_of_notMem Q _ hx

/-- The cylinder restricts every other coordinate to its top cube. Equality of the
integrals follows from pointwise support of the integrand. -/
private theorem coordinate_energy_integral_cylinder
    (I : ∀ i, Box (Fin (d i))) (j : Fin m) (Q : Box (Fin (d j)))
    (hQI : Q ≤ I j) (u v : ProductPoint d → ℝ) (p : ℝ) :
    (∫ x in productBox I,
      (coordinateDifference j Q u x) ^ 2 / Real.rpow (coordinateAverage j Q v x) (2 - p)) =
    ∫ x in productBox (Function.update I j Q),
      (coordinateDifference j Q u x) ^ 2 / Real.rpow (coordinateAverage j Q v x) (2 - p) := by
  have hsub : productBox (Function.update I j Q) ⊆ productBox I := by
    intro x hx
    apply (mem_productBox I x).mpr
    intro i
    by_cases hij : i = j
    · subst i
      apply hQI
      simpa using (mem_productBox (Function.update I j Q) x).mp hx j
    · simpa [hij] using (mem_productBox (Function.update I j Q) x).mp hx i
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_productBox I) hsub
  intro x hx
  have hxQ : x j ∉ Q := by
    intro hxQ
    apply hx.2
    apply (mem_productBox (Function.update I j Q) x).mpr
    intro i
    by_cases hij : i = j
    · subst i
      simpa using hxQ
    · simpa [hij] using (mem_productBox I x).mp hx.1 i
  rw [coordinateDifference_zero_off_parent j Q u x hxQ]
  simp

private theorem coordinate_energy_slice_integral
    (I : ∀ i, Box (Fin (d i))) (j : Fin m) (Q : Box (Fin (d j)))
    (hQI : Q ≤ I j) (u v : ProductPoint d → ℝ) (p : ℝ) (x : ProductPoint d) :
    (∫ y in (I j : Set (Fin (d j) → ℝ)),
      (coordinateDifference j Q u (Function.update x j y)) ^ 2 /
        Real.rpow (coordinateAverage j Q v (Function.update x j y)) (2 - p)) =
    ∫ y in (Q : Set (Fin (d j) → ℝ)),
      (boxDifference Q (fun z => u (Function.update x j z)) y) ^ 2 /
        Real.rpow ((∫ z in (Q : Set (Fin (d j) → ℝ)), v (Function.update x j z)) /
          volume.real (Q : Set (Fin (d j) → ℝ))) (2 - p) := by
  calc
    _ = ∫ y in (Q : Set (Fin (d j) → ℝ)),
        (coordinateDifference j Q u (Function.update x j y)) ^ 2 /
          Real.rpow (coordinateAverage j Q v (Function.update x j y)) (2 - p) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (I j).measurableSet_coe hQI
      intro y hy
      have hyQ0 : y ∉ Q := hy.2
      have hyQ : (Function.update x j y) j ∉ Q := by
        simpa only [Function.update_self] using hyQ0
      rw [coordinateDifference_zero_off_parent j Q u _ hyQ]
      simp
    _ = _ := by
      apply setIntegral_congr_fun Q.measurableSet_coe
      intro y hy
      simp only [coordinateDifference_slice, coordinateAverage, Function.update_self,
        Function.update_idem, boxAverage, Set.indicator_of_mem hy]

private theorem product_leaf_integrable (I : ∀ i, Box (Fin (d i)))
    (N : Fin m → ℕ) (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f) :
    IntegrableOn f (productBox I) volume := by
  have hvol : volume (productBox I) < ⊤ := by
    change Measure.pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
      (Set.pi Set.univ (fun i => (I i : Set (Fin (d i) → ℝ)))) < ⊤
    rw [Measure.pi_pi]
    exact ENNReal.prod_lt_top (fun i _ => (I i).measure_coe_lt_top volume)
  let : IsFiniteMeasure (volume.restrict (productBox I)) :=
    isFiniteMeasure_restrict.mpr hvol.ne
  obtain ⟨A, _, hA⟩ := bounded_product_localization I N f hf
  have hloc : IntegrableOn ((productBox I).indicator f) (productBox I) volume :=
    (integrable_const A).mono'
      (measurable_product_localization I N f hf).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs] using hA x))
  exact hloc.congr_fun (fun x hx => Set.indicator_of_mem hx f)
    (measurableSet_productBox I)

private theorem quotient_leaf_constant (I : ∀ i, Box (Fin (d i)))
    (N : Fin m → ℕ) (u v : ProductPoint d → ℝ) (p : ℝ)
    (hu : ProductLeafConstant I N u) (hv : ProductLeafConstant I N v) :
    ProductLeafConstant I N (fun x => (u x) ^ 2 / Real.rpow (v x) (2 - p)) := by
  intro Q hQ x hx y hy
  change (u x) ^ 2 / Real.rpow (v x) (2 - p) =
    (u y) ^ 2 / Real.rpow (v y) (2 - p)
  rw [hu Q hQ x hx y hy, hv Q hQ x hx y hy]

private theorem coordinateAverage_pos_on_parent
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (v : ProductPoint d → ℝ) (hv : ProductLeafConstant I N v)
    (hvpos : ∀ x ∈ productBox I, 0 < v x)
    (j : Fin m) (Q : Box (Fin (d j))) (hQI : Q ≤ I j)
    (x : ProductPoint d) (hx : x ∈ productBox I) (hxQ : x j ∈ Q) :
    0 < coordinateAverage j Q v x := by
  have hvi := integrableOn_of_leafConstant (I j) (N j)
    (fun y => v (Function.update x j y)) (product_leaf_slice I N v hv j hx)
  have hpos : ∀ y ∈ Q, 0 < v (Function.update x j y) :=
    fun y hy => hvpos _ (update_mem_root I hx j (hQI hy))
  have hnonneg : 0 ≤ᵐ[volume.restrict (Q : Set (Fin (d j) → ℝ))]
      (fun y => v (Function.update x j y)) :=
    (ae_restrict_iff' Q.measurableSet_coe).mpr
      (Filter.Eventually.of_forall (fun y hy => (hpos y hy).le))
  have hsupp : Function.support (fun y => v (Function.update x j y)) ∩
      (Q : Set (Fin (d j) → ℝ)) = Q := by
    apply Set.inter_eq_right.mpr
    intro y hy
    exact ne_of_gt (hpos y hy)
  rw [coordinateAverage_of_mem j Q v x hxQ]
  apply div_pos ?_ (box_volume_pos Q)
  apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg (hvi.mono_set hQI)).mpr
  rw [hsupp]
  exact (ENNReal.toReal_pos_iff.mp (box_volume_pos Q)).1

private theorem coordinate_energy_nonneg
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (u v : ProductPoint d → ℝ) (p : ℝ) (hv : ProductLeafConstant I N v)
    (hvpos : ∀ x ∈ productBox I, 0 < v x)
    (j : Fin m) (Q : Box (Fin (d j))) (hQI : Q ≤ I j)
    (x : ProductPoint d) (hx : x ∈ productBox I) :
    0 ≤ (coordinateDifference j Q u x) ^ 2 /
      Real.rpow (coordinateAverage j Q v x) (2 - p) := by
  by_cases hxQ : x j ∈ Q
  · exact div_nonneg (sq_nonneg _)
      (Real.rpow_pos_of_pos (coordinateAverage_pos_on_parent I N v hv hvpos j Q hQI x hx hxQ)
        (2 - p)).le
  · rw [coordinateDifference_zero_off_parent j Q u x hxQ]
    simp

/-- The exact one-coordinate weighted square estimate, lifted to
integrals over the top rectangle. Only the selected dimension must be positive. -/
theorem coordinate_weighted_square
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (j : Fin m) (hd : 0 < d j)
    (u v : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2)
    (hu : ProductLeafConstant I N u) (hv : ProductLeafConstant I N v)
    (hvpos : ∀ x ∈ productBox I, 0 < v x) :
    (∑ Q ∈ interior (I j) (N j), ∫ x in productBox I,
      (coordinateDifference j Q u x) ^ 2 / Real.rpow (coordinateAverage j Q v x) (2 - p)) ≤
      Real.rpow 2 ((d j : ℝ) * (2 - p)) * ((3 - p) / (p - 1)) *
        ∫ x in productBox I, (u x) ^ 2 / Real.rpow (v x) (2 - p) := by
  let E : Box (Fin (d j)) → ProductPoint d → ℝ := fun Q x =>
    (coordinateDifference j Q u x) ^ 2 / Real.rpow (coordinateAverage j Q v x) (2 - p)
  let H : ProductPoint d → ℝ := fun x => ∑ Q ∈ interior (I j) (N j), E Q x
  let K : ProductPoint d → ℝ := fun x => (u x) ^ 2 / Real.rpow (v x) (2 - p)
  let C : ℝ := Real.rpow 2 ((d j : ℝ) * (2 - p)) * ((3 - p) / (p - 1))
  have hE (Q : Box (Fin (d j))) (hQ : Q ∈ interior (I j) (N j)) :
      ProductLeafConstant I N (E Q) :=
    quotient_leaf_constant I N (coordinateDifference j Q u) (coordinateAverage j Q v) p
      (productLeafConstant_coordinateDifference hu j Q hQ)
      (productLeafConstant_coordinateAverage hv j Q
        (interior_subset_descendants (I j) (N j) hQ))
  have hH : ProductLeafConstant I N H := by
    intro P hP x hx y hy
    change (∑ Q ∈ interior (I j) (N j), E Q x) =
      ∑ Q ∈ interior (I j) (N j), E Q y
    exact Finset.sum_congr rfl (fun Q hQ => hE Q hQ P hP x hx y hy)
  have hK : ProductLeafConstant I N K := quotient_leaf_constant I N u v p hu hv
  have hH0 : ∀ x ∈ productBox I, 0 ≤ H x := by
    intro x hx
    change 0 ≤ ∑ Q ∈ interior (I j) (N j), E Q x
    apply Finset.sum_nonneg
    intro Q hQ
    exact coordinate_energy_nonneg I N u v p hv hvpos j Q
      (le_of_mem_descendants (interior_subset_descendants (I j) (N j) hQ)) x hx
  have hK0 : ∀ x ∈ productBox I, 0 ≤ K x := by
    intro x hx
    exact div_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos (hvpos x hx) (2 - p)).le
  have hC : 0 ≤ C :=
    mul_nonneg (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
      (div_nonneg (by linarith) (by linarith))
  have hslice : ∀ x ∈ productBox I,
      (∫ y in (I j : Set (Fin (d j) → ℝ)), H (Function.update x j y)) ≤
        C * (∫ y in (I j : Set (Fin (d j) → ℝ)), K (Function.update x j y)) := by
    intro x hx
    have hEi (Q : Box (Fin (d j))) (hQ : Q ∈ interior (I j) (N j)) :
        IntegrableOn (fun y => E Q (Function.update x j y))
          (I j : Set (Fin (d j) → ℝ)) volume :=
      integrableOn_of_leafConstant (I j) (N j) _
        (product_leaf_slice I N (E Q) (hE Q hQ) j hx)
    calc
      _ = ∑ Q ∈ interior (I j) (N j), ∫ y in (I j : Set (Fin (d j) → ℝ)),
          E Q (Function.update x j y) :=
        integral_finsetSum (interior (I j) (N j)) hEi
      _ = ∑ Q ∈ interior (I j) (N j), ∫ y in (Q : Set (Fin (d j) → ℝ)),
          (boxDifference Q (fun z => u (Function.update x j z)) y) ^ 2 /
            Real.rpow ((∫ z in (Q : Set (Fin (d j) → ℝ)), v (Function.update x j z)) /
              volume.real (Q : Set (Fin (d j) → ℝ))) (2 - p) := by
        apply Finset.sum_congr rfl
        intro Q hQ
        exact coordinate_energy_slice_integral I j Q
          (le_of_mem_descendants (interior_subset_descendants (I j) (N j) hQ)) u v p x
      _ ≤ _ := weighted_square (d j) hd (I j) (N j)
        (fun y => u (Function.update x j y)) (fun y => v (Function.update x j y)) p hp hp2
        (product_leaf_slice I N u hu j hx) (product_leaf_slice I N v hv j hx)
        (fun y hy => hvpos _ (update_mem_root I hx j hy))
  have h := integral_product_le_of_coordinate_le I N H K hH hK hH0 hK0 C hC j hslice
  have hsum : (∫ x in productBox I, H x) =
      ∑ Q ∈ interior (I j) (N j), ∫ x in productBox I, E Q x :=
    integral_finsetSum (interior (I j) (N j))
      (fun Q hQ => product_leaf_integrable I N (E Q) (hE Q hQ))
  rw [hsum] at h
  exact h

end ReyZygmund
