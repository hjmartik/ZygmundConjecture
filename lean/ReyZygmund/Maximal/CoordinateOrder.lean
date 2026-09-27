import ReyZygmund.Maximal.Coordinate

/-! # Order properties of the coordinate maximal function

The positive maximal function dominates the absolute value of each coordinate
average. Domination of absolute inputs on the top rectangle implies domination of
their maximal functions there. The finite step-function hypotheses give the slice
integrability.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}
variable {I : ∀ i, Box (Fin (d i))} {N : Fin m → ℕ}

private theorem update_mem_product_root {x : ProductPoint d}
    (hx : x ∈ productBox I) (i : Fin m) {y : Fin (d i) → ℝ} (hy : y ∈ I i) :
    Function.update x i y ∈ productBox I := by
  apply (mem_productBox I _).mpr
  intro j
  by_cases hji : j = i
  · subst j
    simpa using hy
  · simpa [hji] using (mem_productBox I x).mp hx j

private theorem root_slice_integrable {f : ProductPoint d → ℝ}
    (hf : ProductLeafConstant I N f) (i : Fin m) (Q : Box (Fin (d i)))
    (hQI : Q ≤ I i) (x : ProductPoint d) (hx : x ∈ productBox I) :
    IntegrableOn (fun y => f (Function.update x i y))
      (Q : Set (Fin (d i) → ℝ)) volume := by
  obtain ⟨C, _, hC⟩ := bounded_product_localization I N f hf
  have hloc := integrable_coordinateSlice ((productBox I).indicator f)
    (measurable_product_localization I N f hf) C hC i Q x
  exact hloc.congr_fun
    (fun y hy => Set.indicator_of_mem (update_mem_product_root hx i (hQI hy)) f)
    Q.measurableSet_coe

private theorem average_absolute_nonneg (i : Fin m) (Q : Box (Fin (d i)))
    (f : ProductPoint d → ℝ) (x : ProductPoint d) :
    0 ≤ coordinateAverage i Q (fun y => |f y|) x := by
  by_cases hxQ : x i ∈ Q
  · rw [coordinateAverage_of_mem i Q (fun y => |f y|) x hxQ]
    exact div_nonneg (integral_nonneg (fun y => abs_nonneg (f (Function.update x i y))))
      (box_volume_pos Q).le
  · simp only [coordinateAverage_of_notMem i Q (fun y => |f y|) x hxQ, le_refl]

/-- The finite positive maximal function dominates each retained coordinate average on
the top rectangle, also for signed inputs. -/
theorem abs_coordinateAverage_le_coordinateDyadicMaximal
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (i : Fin m) (Q : Box (Fin (d i))) (hQ : Q ∈ descendants (I i) (N i))
    (x : ProductPoint d) (hx : x ∈ productBox I) :
    |coordinateAverage i Q f x| ≤ coordinateDyadicMaximal i (I i) (N i) f x := by
  have hmean : |coordinateAverage i Q f x| ≤
      coordinateAverage i Q (fun y => |f y|) x := by
    by_cases hxQ : x i ∈ Q
    · have hfi := root_slice_integrable hf i Q (le_of_mem_descendants hQ) x hx
      have hfai : IntegrableOn (fun y => |f (Function.update x i y)|)
          (Q : Set (Fin (d i) → ℝ)) volume := by
        simpa only [IntegrableOn, Real.norm_eq_abs] using hfi.norm
      rw [coordinateAverage_of_mem i Q f x hxQ,
        coordinateAverage_of_mem i Q (fun y => |f y|) x hxQ,
        abs_div, abs_of_pos (box_volume_pos Q)]
      apply div_le_div_of_nonneg_right _ (box_volume_pos Q).le
      apply abs_le.mpr
      constructor
      · have h := integral_mono hfai.neg hfi
          (fun y => neg_abs_le (f (Function.update x i y)))
        simpa only [Pi.neg_apply, integral_neg] using h
      · exact integral_mono hfi hfai (fun y => le_abs_self (f (Function.update x i y)))
    · simp only [coordinateAverage_of_notMem i Q f x hxQ,
        coordinateAverage_of_notMem i Q (fun y => |f y|) x hxQ, abs_zero, le_refl]
  refine hmean.trans ?_
  obtain ⟨n, hn, hQn⟩ := mem_descendants.mp hQ
  rw [coordinateDyadicMaximal_eq_level_sup]
  apply Finset.le_sup'_of_le _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  exact Finset.single_le_sum (fun R _ => average_absolute_nonneg i R f x) hQn

/-- Domination of absolute inputs on the top rectangle gives domination of their
coordinate maximal functions there. -/
theorem coordinateDyadicMaximal_mono_abs
    (f g : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hg : ProductLeafConstant I N g)
    (hfg : ∀ y ∈ productBox I, |f y| ≤ |g y|)
    (i : Fin m) (x : ProductPoint d) (hx : x ∈ productBox I) :
    coordinateDyadicMaximal i (I i) (N i) f x ≤
      coordinateDyadicMaximal i (I i) (N i) g x := by
  rw [coordinateDyadicMaximal_eq_level_sup, coordinateDyadicMaximal_eq_level_sup]
  apply Finset.sup'_mono_fun
  intro n _
  apply Finset.sum_le_sum
  intro Q hQ
  by_cases hxQ : x i ∈ Q
  · have hQI := (level (I i) n).le_of_mem hQ
    have hfi := root_slice_integrable hf i Q hQI x hx
    have hgi := root_slice_integrable hg i Q hQI x hx
    have hfai : IntegrableOn (fun y => |f (Function.update x i y)|)
        (Q : Set (Fin (d i) → ℝ)) volume := by
      simpa only [IntegrableOn, Real.norm_eq_abs] using hfi.norm
    have hgai : IntegrableOn (fun y => |g (Function.update x i y)|)
        (Q : Set (Fin (d i) → ℝ)) volume := by
      simpa only [IntegrableOn, Real.norm_eq_abs] using hgi.norm
    rw [coordinateAverage_of_mem i Q (fun y => |f y|) x hxQ,
      coordinateAverage_of_mem i Q (fun y => |g y|) x hxQ]
    apply div_le_div_of_nonneg_right _ (box_volume_pos Q).le
    exact setIntegral_mono_on hfai hgai Q.measurableSet_coe
      (fun y hy => hfg _ (update_mem_product_root hx i (hQI hy)))
  · simp only [coordinateAverage_of_notMem i Q (fun y => |f y|) x hxQ,
      coordinateAverage_of_notMem i Q (fun y => |g y|) x hxQ, le_refl]

end ReyZygmund
