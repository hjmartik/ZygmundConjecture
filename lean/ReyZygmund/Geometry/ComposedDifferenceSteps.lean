import ReyZygmund.Geometry.ProductSteps

/-!
# Finite step properties of composed coordinate differences

For a real-valued input, the fixed-order product difference is supported on its
indexing rectangle and constant on every product of children. These pointwise
slice identities imply measurability and a finite absolute bound.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- A coordinate difference vanishes outside its parent coordinate cube. -/
theorem coordinateDifference_eq_zero_of_notMem (i : Fin m)
    (Q : Box (Fin (d i))) (f : ProductPoint d → ℝ)
    (x : ProductPoint d) (hx : x i ∉ Q) : coordinateDifference i Q f x = 0 := by
  rw [coordinateDifference_eq_sum]
  simp only [Pi.sub_apply, Finset.sum_apply]
  rw [coordinateAverage_of_notMem i Q f x hx, sub_zero]
  apply Finset.sum_eq_zero
  intro R hR
  exact coordinateAverage_of_notMem i R f x
    (fun h => hx ((Prepartition.splitCenter Q).le_of_mem hR h))

/-- If the whole coordinate slice is zero, its coordinate difference is zero. -/
theorem coordinateDifference_eq_zero_of_slice_eq_zero (i : Fin m)
    (Q : Box (Fin (d i))) (f : ProductPoint d → ℝ) (x : ProductPoint d)
    (hf : ∀ y, f (Function.update x i y) = 0) : coordinateDifference i Q f x = 0 := by
  have hslice : (fun y => f (Function.update x i y)) = 0 := funext hf
  simp [coordinateDifference, hslice, cubeDifference, cubeAverage, cubeMean]

/-- Equal updated slices give equal difference values at points in one child. -/
theorem coordinateDifference_eq_on_child (i : Fin m)
    {Q R : Box (Fin (d i))} (hR : R ∈ Prepartition.splitCenter Q)
    (f : ProductPoint d → ℝ) (x y : ProductPoint d)
    (hx : x i ∈ R) (hy : y i ∈ R)
    (hxy : ∀ z, f (Function.update x i z) = f (Function.update y i z)) :
    coordinateDifference i Q f x = coordinateDifference i Q f y := by
  have hslice : (fun z => f (Function.update x i z)) =
      (fun z => f (Function.update y i z)) := funext hxy
  simp only [coordinateDifference, cubeDifference_apply_child hR _ hx,
    cubeDifference_apply_child hR _ hy, hslice]

/-- Support in any coordinate in a composition is preserved by the other factors. -/
theorem foldr_coordinateDifference_eq_zero_of_notMem
    (L : List (Fin m)) (Q : ∀ i, Box (Fin (d i))) (f : ProductPoint d → ℝ)
    (j : Fin m) (hj : j ∈ L) (x : ProductPoint d) (hx : x j ∉ Q j) :
    L.foldr (fun i g => coordinateDifference i (Q i) g) f x = 0 := by
  induction L generalizing x with
  | nil => simp at hj
  | cons i L ih =>
    simp only [List.foldr_cons]
    by_cases hji : j = i
    · subst j
      exact coordinateDifference_eq_zero_of_notMem i (Q i) _ x hx
    · apply coordinateDifference_eq_zero_of_slice_eq_zero
      intro y
      apply ih ((List.mem_cons.mp hj).resolve_left hji)
      simpa [Function.update_of_ne hji] using hx

/-- A composition in distinct coordinates is constant on the selected product
children when the remaining coordinates are fixed. -/
theorem foldr_coordinateDifference_eq_on_children
    (L : List (Fin m)) (hL : L.Nodup)
    (Q R : ∀ i, Box (Fin (d i)))
    (hR : ∀ i ∈ L, R i ∈ Prepartition.splitCenter (Q i))
    (f : ProductPoint d → ℝ) (x y : ProductPoint d)
    (hx : ∀ i ∈ L, x i ∈ R i) (hy : ∀ i ∈ L, y i ∈ R i)
    (hxy : ∀ i ∉ L, x i = y i) :
    L.foldr (fun i g => coordinateDifference i (Q i) g) f x =
      L.foldr (fun i g => coordinateDifference i (Q i) g) f y := by
  induction L generalizing x y with
  | nil =>
    have h : x = y := funext (fun i => hxy i (by simp))
    simp [h]
  | cons i L ih =>
    simp only [List.foldr_cons]
    apply coordinateDifference_eq_on_child i (hR i (by simp)) _ x y
      (hx i (by simp)) (hy i (by simp))
    intro z
    apply ih hL.of_cons (fun j hj => hR j (by simp [hj]))
    · intro j hj
      have hji : j ≠ i := fun h => (List.nodup_cons.mp hL).1 (h ▸ hj)
      simpa [Function.update_of_ne hji] using hx j (by simp [hj])
    · intro j hj
      have hji : j ≠ i := fun h => (List.nodup_cons.mp hL).1 (h ▸ hj)
      simpa [Function.update_of_ne hji] using hy j (by simp [hj])
    · intro j hj
      by_cases hji : j = i
      · subst j
        simp
      · simpa [Function.update_of_ne hji] using hxy j (by simp [hji, hj])

/-- The partial composition may be indexed by the sorted coordinate set. -/
theorem partialDifference_eq_foldr (A : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) (f : ProductPoint d → ℝ) :
    MathlibOnly.partialDifference A (fun i => Q i) f =
      (A.sort (· ≤ ·)).foldr (fun i g => coordinateDifference i (Q i) g) f := by
  classical
  let e : A ↪ Fin m := ⟨Subtype.val, Subtype.val_injective⟩
  have he : (Finset.univ : Finset A).map e = A := by
    ext i
    simp [e]
  have hs := Finset.map_sort e (Finset.univ : Finset A) (· ≤ ·) (· ≤ ·)
    (fun _ _ _ _ => Iff.rfl)
  rw [he] at hs
  rw [← hs, List.foldr_map]
  rfl

/-- The full difference is zero off its indexing rectangle. -/
theorem fullDifference_eq_zero_of_notMem
    (Q : ∀ i, Box (Fin (d i))) (f : ProductPoint d → ℝ)
    (x : ProductPoint d) (hx : x ∉ MathlibOnly.productRectangle Q) :
    MathlibOnly.fullDifference Q f x = 0 := by
  change ¬ ∀ i, x i ∈ Q i at hx
  obtain ⟨i, hi⟩ := not_forall.mp hx
  rw [MathlibOnly.fullDifference, partialDifference_eq_foldr]
  exact foldr_coordinateDifference_eq_zero_of_notMem _ Q f i (by simp) x hi

/-- The full difference is constant on each product of child cubes. -/
theorem fullDifference_eq_on_children
    (Q R : ∀ i, Box (Fin (d i)))
    (hR : ∀ i, R i ∈ Prepartition.splitCenter (Q i)) (f : ProductPoint d → ℝ)
    (x : ProductPoint d) (hx : x ∈ MathlibOnly.productRectangle R)
    (y : ProductPoint d) (hy : y ∈ MathlibOnly.productRectangle R) :
    MathlibOnly.fullDifference Q f x = MathlibOnly.fullDifference Q f y := by
  rw [MathlibOnly.fullDifference, partialDifference_eq_foldr]
  apply foldr_coordinateDifference_eq_on_children _ (Finset.sort_nodup _ _) Q R
    (fun i _ => hR i) f x y (fun i _ => hx i) (fun i _ => hy i)
  intro i hi
  simp at hi

theorem productLeafConstant_fullDifference
    (Q : ∀ i, Box (Fin (d i))) (f : ProductPoint d → ℝ) :
    ProductLeafConstant Q (fun _ => 1) (MathlibOnly.fullDifference Q f) := by
  intro R hR x hx y hy
  apply fullDifference_eq_on_children Q R ?_ f x
    ((mem_productRectangle R x).mp hx) y ((mem_productRectangle R y).mp hy)
  intro i
  have hi := Fintype.mem_piFinset.mp hR i
  simpa [leaves, level] using hi

theorem indicator_fullDifference
    (Q : ∀ i, Box (Fin (d i))) (f : ProductPoint d → ℝ) :
    (MathlibOnly.productRectangle Q).indicator (MathlibOnly.fullDifference Q f) =
      MathlibOnly.fullDifference Q f := by
  funext x
  by_cases hx : x ∈ MathlibOnly.productRectangle Q
  · exact Set.indicator_of_mem hx _
  · rw [Set.indicator_of_notMem hx, fullDifference_eq_zero_of_notMem Q f x hx]

/-- The child partition makes the full difference a measurable step function. -/
theorem measurable_fullDifference
    (Q : ∀ i, Box (Fin (d i))) (f : ProductPoint d → ℝ) :
    Measurable (MathlibOnly.fullDifference Q f) := by
  have h := measurable_product_localization Q (fun _ => 1)
    (MathlibOnly.fullDifference Q f) (productLeafConstant_fullDifference Q f)
  rwa [indicator_fullDifference] at h

/-- Finitely many child values give a finite real bound. -/
theorem bounded_fullDifference
    (Q : ∀ i, Box (Fin (d i))) (f : ProductPoint d → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |MathlibOnly.fullDifference Q f x| ≤ C := by
  have h := bounded_product_localization Q (fun _ => 1)
    (MathlibOnly.fullDifference Q f) (productLeafConstant_fullDifference Q f)
  rwa [indicator_fullDifference] at h

theorem measurable_sum_fullDifference
    (H : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ) :
    Measurable (fun x => ∑ Q ∈ H, MathlibOnly.fullDifference Q f x) :=
  H.measurable_sum (fun Q _ => measurable_fullDifference Q f)

theorem bounded_sum_fullDifference
    (H : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |∑ Q ∈ H, MathlibOnly.fullDifference Q f x| ≤ C := by
  classical
  choose C hC hb using (fun Q : ∀ i, Box (Fin (d i)) => bounded_fullDifference Q f)
  refine ⟨∑ Q ∈ H, C Q, Finset.sum_nonneg (fun Q _ => hC Q), ?_⟩
  intro x
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun Q _ => hb Q x))

end ReyZygmund.Geometry
