import ReyZygmund.Maximal.GlobalCoordinateDefs

/-! # Coordinate averages and maxima on the whole grid

The operators keep extended nonnegative values. Their support, measurability,
order and update identities require no finite-integral convention. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

theorem coordinateGridAverage_of_mem (j : Fin m) (Q : Box (Fin (d j)))
    (F : ProductPoint d → ℝ≥0∞) (x : ProductPoint d) (hx : x j ∈ Q) :
    coordinateGridAverage j Q F x =
      (volume (Q : Set (Fin (d j) → ℝ)))⁻¹ *
        ∫⁻ y in (Q : Set (Fin (d j) → ℝ)), F (Function.update x j y) := by
  exact Set.indicator_of_mem hx _

theorem coordinateGridAverage_of_notMem (j : Fin m) (Q : Box (Fin (d j)))
    (F : ProductPoint d → ℝ≥0∞) (x : ProductPoint d) (hx : x j ∉ Q) :
    coordinateGridAverage j Q F x = 0 := by
  exact Set.indicator_of_notMem hx _

theorem measurable_coordinateGridAverage (j : Fin m) (Q : Box (Fin (d j)))
    (F : ProductPoint d → ℝ≥0∞) (hF : Measurable F) :
    Measurable (coordinateGridAverage j Q F) := by
  have hi : Measurable (fun x : ProductPoint d =>
      ∫⁻ y in (Q : Set (Fin (d j) → ℝ)), F (Function.update x j y)) :=
    Measurable.lintegral_prod_right (hF.comp (measurable_update' (a := j)))
  exact (hi.const_mul _).indicator
    (Q.measurableSet_coe.preimage (measurable_pi_apply j))

theorem coordinateGridAverage_mono (j : Fin m) (Q : Box (Fin (d j)))
    (F G : ProductPoint d → ℝ≥0∞) (hFG : F ≤ G) :
    coordinateGridAverage j Q F ≤ coordinateGridAverage j Q G := by
  intro x
  by_cases hx : x j ∈ Q
  · rw [coordinateGridAverage_of_mem j Q F x hx,
      coordinateGridAverage_of_mem j Q G x hx]
    exact mul_le_mul' le_rfl (lintegral_mono (fun y => hFG (Function.update x j y)))
  · rw [coordinateGridAverage_of_notMem j Q F x hx,
      coordinateGridAverage_of_notMem j Q G x hx]

theorem coordinateGridAverage_update (j : Fin m) (Q : Box (Fin (d j)))
    (F : ProductPoint d → ℝ≥0∞) (x : ProductPoint d) (y : Fin (d j) → ℝ) :
    coordinateGridAverage j Q F (Function.update x j y) =
      (Q : Set (Fin (d j) → ℝ)).indicator
        (fun _ => (volume (Q : Set (Fin (d j) → ℝ)))⁻¹ *
          ∫⁻ z in (Q : Set (Fin (d j) → ℝ)), F (Function.update x j z)) y := by
  by_cases hy : y ∈ Q
  · rw [coordinateGridAverage_of_mem j Q F _ (by
        simpa only [Function.update_self] using hy), Set.indicator_of_mem hy]
    simp only [Function.update_idem]
  · rw [coordinateGridAverage_of_notMem j Q F _ (by
        simpa only [Function.update_self] using hy), Set.indicator_of_notMem hy]

theorem measurable_coordinateGridMaximal (D : ∀ i, DyadicGrid (d i)) (j : Fin m)
    (F : ProductPoint d → ℝ≥0∞) (hF : Measurable F) :
    Measurable (coordinateGridMaximal D j F) := by
  have hc : {Q : Box (Fin (d j)) | ∃ n : ℤ, Q ∈ (D j).cubes n}.Countable := by
    have heq : (⋃ n : ℤ, (D j).cubes n) =
        {Q : Box (Fin (d j)) | ∃ n : ℤ, Q ∈ (D j).cubes n} := by
      ext Q
      simp
    rw [← heq]
    exact (D j).countable_all_cubes
  have := hc.to_subtype
  exact Measurable.iSup (fun Q => measurable_coordinateGridAverage j Q.1 F hF)

theorem coordinateGridMaximal_mono (D : ∀ i, DyadicGrid (d i)) (j : Fin m)
    (F G : ProductPoint d → ℝ≥0∞) (hFG : F ≤ G) :
    coordinateGridMaximal D j F ≤ coordinateGridMaximal D j G := by
  intro x
  exact iSup_mono (fun Q => coordinateGridAverage_mono j Q.1 F G hFG x)

theorem coordinateGridAverage_le_maximal (D : ∀ i, DyadicGrid (d i)) (j : Fin m)
    (Q : Box (Fin (d j))) (hQ : ∃ n : ℤ, Q ∈ (D j).cubes n)
    (F : ProductPoint d → ℝ≥0∞) (x : ProductPoint d) :
    coordinateGridAverage j Q F x ≤ coordinateGridMaximal D j F x :=
  le_iSup (fun Q : {Q : Box (Fin (d j)) | ∃ n : ℤ, Q ∈ (D j).cubes n} =>
    coordinateGridAverage j Q.1 F x) ⟨Q, hQ⟩

theorem coordinateGridMaximal_update (D : ∀ i, DyadicGrid (d i)) (j : Fin m)
    (F : ProductPoint d → ℝ≥0∞) (x : ProductPoint d) (y : Fin (d j) → ℝ) :
    coordinateGridMaximal D j F (Function.update x j y) =
      ⨆ Q : {Q : Box (Fin (d j)) | ∃ n : ℤ, Q ∈ (D j).cubes n},
        (Q.1 : Set (Fin (d j) → ℝ)).indicator
          (fun _ => (volume (Q.1 : Set (Fin (d j) → ℝ)))⁻¹ *
            ∫⁻ z in (Q.1 : Set (Fin (d j) → ℝ)), F (Function.update x j z)) y := by
  simp only [coordinateGridMaximal, coordinateGridAverage_update]

theorem measurable_foldr_coordinateGridMaximal
    (D : ∀ i, DyadicGrid (d i)) (order : List (Fin m))
    (F : ProductPoint d → ℝ≥0∞) (hF : Measurable F) :
    Measurable (order.foldr (fun j G => coordinateGridMaximal D j G) F) := by
  induction order with
  | nil => exact hF
  | cons j order ih => exact measurable_coordinateGridMaximal D j _ ih

theorem measurable_iteratedGridMaximal (D : ∀ i, DyadicGrid (d i))
    (F : ProductPoint d → ℝ≥0∞) (hF : Measurable F) :
    Measurable (iteratedGridMaximal D F) :=
  measurable_foldr_coordinateGridMaximal D (List.finRange m) F hF

private theorem normalized_lmarginal_le_foldr
    (D : ∀ i, DyadicGrid (d i)) (Q : ∀ i, Box (Fin (d i)))
    (hQ : Q ∈ gridRectangles D) (F : ProductPoint d → ℝ≥0∞) (hF : Measurable F)
    (order : List (Fin m)) :
    order.Nodup → ∀ x : ProductPoint d, (∀ i ∈ order, x i ∈ Q i) →
      (∏ i ∈ order.toFinset, (volume (Q i : Set (Fin (d i) → ℝ)))⁻¹) *
          lmarginal (fun i => volume.restrict (Q i : Set (Fin (d i) → ℝ)))
            order.toFinset F x ≤
        order.foldr (fun j G => coordinateGridMaximal D j G) F x := by
  let μ : ∀ i : Fin m, Measure (Fin (d i) → ℝ) :=
    fun i => volume.restrict (Q i : Set (Fin (d i) → ℝ))
  induction order with
  | nil =>
      intro _ x _
      simp
  | cons j order ih =>
      intro hn x hx
      have hn' := List.nodup_cons.mp hn
      have hj : j ∉ order.toFinset := by simpa only [List.mem_toFinset] using hn'.1
      have htail (y : Fin (d j) → ℝ) : ∀ i ∈ order, Function.update x j y i ∈ Q i := by
        intro i hi
        have hij : i ≠ j := by
          intro h
          exact hn'.1 (h ▸ hi)
        rw [Function.update_of_ne hij]
        exact hx i (List.mem_cons_of_mem j hi)
      have hm : Measurable (fun y : Fin (d j) → ℝ =>
          lmarginal μ order.toFinset F (Function.update x j y)) :=
        (hF.lmarginal μ).comp (measurable_update x)
      change (∏ i ∈ (j :: order).toFinset,
          (volume (Q i : Set (Fin (d i) → ℝ)))⁻¹) *
          lmarginal μ (j :: order).toFinset F x ≤
        coordinateGridMaximal D j
          (order.foldr (fun i G => coordinateGridMaximal D i G) F) x
      rw [List.toFinset_cons, Finset.prod_insert hj, lmarginal_insert F hF hj x]
      calc
        _ = (volume (Q j : Set (Fin (d j) → ℝ)))⁻¹ *
            ∫⁻ y, (∏ i ∈ order.toFinset,
                (volume (Q i : Set (Fin (d i) → ℝ)))⁻¹) *
              lmarginal μ order.toFinset F (Function.update x j y) ∂μ j := by
          rw [lintegral_const_mul _ hm, mul_assoc]
        _ ≤ (volume (Q j : Set (Fin (d j) → ℝ)))⁻¹ *
            ∫⁻ y, order.foldr (fun i G => coordinateGridMaximal D i G) F
              (Function.update x j y) ∂μ j := by
          exact mul_le_mul' le_rfl (lintegral_mono (fun y =>
            ih hn'.2 (Function.update x j y) (htail y)))
        _ = coordinateGridAverage j (Q j)
            (order.foldr (fun i G => coordinateGridMaximal D i G) F) x := by
          symm
          exact coordinateGridAverage_of_mem j (Q j) _ x (hx j (by simp))
        _ ≤ _ := coordinateGridAverage_le_maximal D j (Q j) (hQ j) _ x

/-- Every rectangular average is dominated by the ordered full-grid
coordinate composition, including when the integral is infinite. -/
theorem productAverage_le_iteratedGridMaximal (D : ∀ i, DyadicGrid (d i))
    (F : ProductPoint d → ℝ≥0∞) (hF : Measurable F)
    (Q : ∀ i, Box (Fin (d i))) (hQ : Q ∈ gridRectangles D)
    (x : ProductPoint d) :
    (productBox Q).indicator
      (fun _ => (volume (productBox Q))⁻¹ * ∫⁻ y in productBox Q, F y) x ≤
        iteratedGridMaximal D F x := by
  by_cases hx : x ∈ productBox Q
  · rw [Set.indicator_of_mem hx]
    have hfin : (List.finRange m).toFinset = Finset.univ := by
      ext i
      simp
    have hvol : volume (productBox Q) =
        ∏ i, volume (Q i : Set (Fin (d i) → ℝ)) :=
      Measure.pi_pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
        (fun i => (Q i : Set (Fin (d i) → ℝ)))
    have hinv : (volume (productBox Q))⁻¹ =
        ∏ i, (volume (Q i : Set (Fin (d i) → ℝ)))⁻¹ := by
      rw [hvol]
      apply ENNReal.prod_inv_distrib
      intro i _ j _ _
      exact Or.inr ((Q j).measure_coe_lt_top volume).ne
    have hrestrict : volume.restrict (productBox Q) =
        Measure.pi (fun i => volume.restrict (Q i : Set (Fin (d i) → ℝ))) :=
      Measure.restrict_pi_pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
        (fun i => (Q i : Set (Fin (d i) → ℝ)))
    have h := normalized_lmarginal_le_foldr D Q hQ F hF (List.finRange m)
      (List.nodup_finRange m) x (fun i _ => (mem_productBox Q x).mp hx i)
    simpa only [hfin, lmarginal_univ, hinv, hrestrict, iteratedGridMaximal] using h
  · rw [Set.indicator_of_notMem hx]
    exact zero_le

end ReyZygmund
