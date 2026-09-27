import ReyZygmund.Geometry.ProductSteps

/-!
# Coordinate algebra on bounded measurable functions

The finite inputs in the paper belong to this class after zero extension.
All slice integrability used in linearity and Fubini is derived, not assumed as
an operator law. The estimates for a difference use the unique child containing
the point and therefore do not lose a factor equal to the number of children.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

theorem coordinateAverage_abs_le (i : Fin m) (Q : Box (Fin (d i)))
    (f : ProductPoint d → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ C)
    (x : ProductPoint d) : |coordinateAverage i Q f x| ≤ C := by
  by_cases hx : x i ∈ Q
  · rw [coordinateAverage_of_mem i Q f x hx, abs_div,
      abs_of_pos (box_volume_pos Q)]
    apply (div_le_iff₀ (box_volume_pos Q)).mpr
    let : IsFiniteMeasure (volume.restrict (Q : Set (Fin (d i) → ℝ))) :=
      isFiniteMeasure_restrict.mpr (Q.measure_coe_lt_top volume).ne
    have h := norm_integral_le_of_norm_le_const
      (μ := volume.restrict (Q : Set (Fin (d i) → ℝ)))
      (f := fun y => f (Function.update x i y))
      (Filter.Eventually.of_forall (fun y => by
        simpa [Real.norm_eq_abs] using hf (Function.update x i y)))
    simpa [Real.norm_eq_abs, Measure.real] using h
  · rw [coordinateAverage_of_notMem i Q f x hx, abs_zero]
    exact hC

theorem coordinateDifference_measurable (i : Fin m) (Q : Box (Fin (d i)))
    (f : ProductPoint d → ℝ) (hf : Measurable f) :
    Measurable (coordinateDifference i Q f) := by
  have hs : Measurable (fun x => ∑ R ∈ (Prepartition.splitCenter Q).boxes,
      coordinateAverage i R f x) :=
    Finset.measurable_sum _ (fun R _ => coordinateAverage_measurable i R f hf)
  convert hs.sub (coordinateAverage_measurable i Q f hf) using 1
  ext x
  simp only [coordinateDifference, Pi.sub_apply, Finset.sum_apply]

theorem coordinateDifference_abs_le (i : Fin m) (Q : Box (Fin (d i)))
    (f : ProductPoint d → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ C)
    (x : ProductPoint d) : |coordinateDifference i Q f x| ≤ 2 * C := by
  have hs : |∑ R ∈ (Prepartition.splitCenter Q).boxes, coordinateAverage i R f x| ≤ C := by
    by_cases hx : x i ∈ Q
    · obtain ⟨R, hR, hxR⟩ := Prepartition.isPartition_splitCenter Q (x i) hx
      rw [Finset.sum_eq_single R]
      · exact coordinateAverage_abs_le i R f C hC hf x
      · intro S hS hSR
        exact coordinateAverage_of_notMem i S f x (fun hxS =>
          hSR ((Prepartition.splitCenter Q).eq_of_mem_of_mem hS hR hxS hxR))
      · simp [hR]
    · rw [Finset.sum_eq_zero (fun R hR => coordinateAverage_of_notMem i R f x
        (fun hxR => hx ((Prepartition.splitCenter Q).le_of_mem hR hxR))), abs_zero]
      exact hC
  simp only [coordinateDifference, Pi.sub_apply, Finset.sum_apply]
  calc
    _ ≤ |∑ R ∈ (Prepartition.splitCenter Q).boxes, coordinateAverage i R f x| +
        |coordinateAverage i Q f x| := abs_sub _ _
    _ ≤ C + C := add_le_add hs (coordinateAverage_abs_le i Q f C hC hf x)
    _ = 2 * C := by ring

/-- An average commutes with a difference in a different coordinate. -/
theorem coordinateAverage_difference_commute (i j : Fin m) (hij : i ≠ j)
    (Q : Box (Fin (d i))) (R : Box (Fin (d j))) (f : ProductPoint d → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, |f x| ≤ C) :
    coordinateAverage i Q (coordinateDifference j R f) =
      coordinateDifference j R (coordinateAverage i Q f) := by
  have hi (S : Box (Fin (d j))) (x : ProductPoint d) :
      IntegrableOn (fun y => coordinateAverage j S f (Function.update x i y))
        (Q : Set (Fin (d i) → ℝ)) volume :=
    integrable_coordinateSlice _ (coordinateAverage_measurable j S f hf) C
      (coordinateAverage_abs_le j S f C hC hbound) i Q x
  have hs (x : ProductPoint d) : IntegrableOn
      (fun y => (∑ S ∈ (Prepartition.splitCenter R).boxes, coordinateAverage j S f)
        (Function.update x i y)) (Q : Set (Fin (d i) → ℝ)) volume := by
    simpa only [IntegrableOn, Finset.sum_apply] using
      integrable_finsetSum (Prepartition.splitCenter R).boxes (fun S _ => hi S x)
  have hc (S : Box (Fin (d j))) :
      coordinateAverage i Q (coordinateAverage j S f) =
        coordinateAverage j S (coordinateAverage i Q f) :=
    coordinateAverage_commute i j hij Q S f
      (fun x => integrable_twoCoordinateSlice f hf C hbound i j Q S x)
  unfold coordinateDifference
  rw [coordinateAverage_sub i Q _ _ hs (hi R),
    coordinateAverage_finsetSum (Prepartition.splitCenter R).boxes i Q _
      (fun S _ => hi S), hc R]
  congr 1
  exact Finset.sum_congr rfl (fun S _ => hc S)

/-- Two differences commute in different coordinates. -/
theorem coordinateDifference_commute (i j : Fin m) (hij : i ≠ j)
    (Q : Box (Fin (d i))) (R : Box (Fin (d j))) (f : ProductPoint d → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, |f x| ≤ C) :
    coordinateDifference i Q (coordinateDifference j R f) =
      coordinateDifference j R (coordinateDifference i Q f) := by
  have hleft (S : Box (Fin (d i))) :=
    coordinateAverage_difference_commute i j hij S R f hf C hC hbound
  have hright (T : Box (Fin (d j))) :=
    coordinateAverage_difference_commute j i hij.symm T Q f hf C hC hbound
  have hc (S : Box (Fin (d i))) (T : Box (Fin (d j))) :=
    coordinateAverage_commute i j hij S T f
      (fun x => integrable_twoCoordinateSlice f hf C hbound i j S T x)
  calc
    _ = (∑ S ∈ (Prepartition.splitCenter Q).boxes,
          coordinateDifference j R (coordinateAverage i S f)) -
        coordinateDifference j R (coordinateAverage i Q f) := by
      change (∑ S ∈ (Prepartition.splitCenter Q).boxes,
        coordinateAverage i S (coordinateDifference j R f)) -
          coordinateAverage i Q (coordinateDifference j R f) = _
      simp_rw [hleft]
    _ = (∑ T ∈ (Prepartition.splitCenter R).boxes,
          coordinateDifference i Q (coordinateAverage j T f)) -
        coordinateDifference i Q (coordinateAverage j R f) := by
      simp only [coordinateDifference, Finset.sum_sub_distrib]
      simp_rw [← hc]
      rw [Finset.sum_comm]
      abel
    _ = _ := by
      change _ = (∑ T ∈ (Prepartition.splitCenter R).boxes,
        coordinateAverage j T (coordinateDifference i Q f)) -
          coordinateAverage j R (coordinateDifference i Q f)
      simp_rw [hright]

end ReyZygmund.Geometry
