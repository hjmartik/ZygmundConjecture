import ReyZygmund.Maximal.CoordinateOrder
import ReyZygmund.Maximal.IteratedCoordinate
import ReyZygmund.Geometry.ProductAverageProperties
import ReyZygmund.Geometry.ProductMean
import ReyZygmund.Projection.AveragingRectangles

/-! # The finite maximal function over coordinate products

Compose the supported coordinate averages of the absolute input and take the
maximum over retained product descendants. Unused tuple coordinates repeat a value
without changing the maximum. For the empty coordinate set the result is the
absolute input.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

private def absoluteInput (F : boundedMeasurableFunctions d) :
    boundedMeasurableFunctions d :=
  ⟨fun x => |F.1 x|, by simpa only [Real.norm_eq_abs] using F.2.1.norm, by
    obtain ⟨C, hC, hb⟩ := F.2.2
    exact ⟨C, hC, fun x => by simpa only [abs_abs] using hb x⟩⟩

private theorem product_average_nonneg (F : boundedMeasurableFunctions d)
    (hF : ∀ x, 0 ≤ F.1 x) (A : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) (x : ProductPoint d) :
    0 ≤ (productAverageMap A Q F).1 x := by
  induction A using Finset.induction_on generalizing x with
  | empty => simpa using hF x
  | @insert i A hi ih =>
    rw [productAverageMap_insert A i hi Q, Module.End.mul_apply, averageMap_apply]
    by_cases hx : x i ∈ Q i
    · rw [coordinateAverage_of_mem i (Q i) _ x hx]
      exact div_nonneg (integral_nonneg (fun y => ih (Function.update x i y)))
        (box_volume_pos (Q i)).le
    · rw [coordinateAverage_of_notMem i (Q i) _ x hx]

/-- The finite maximum of positive coordinate-product averages. -/
noncomputable def finiteProductMaximal
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A : Finset (Fin m)) (F : boundedMeasurableFunctions d)
    (x : ProductPoint d) : ℝ :=
  (productDescendants I N).sup' ⟨I, root_mem_productDescendants I N⟩
    (fun Q => (productAverageMap A Q (absoluteInput F)).1 x)

/-- In all coordinates these are precisely the normalized integrals of the
absolute input over the product rectangles. -/
theorem finiteProductMaximal_univ_eq_integral
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) :
    finiteProductMaximal I N Finset.univ F x =
      (productDescendants I N).sup' ⟨I, root_mem_productDescendants I N⟩
        (fun Q => (productBox Q).indicator
          (fun _ => (∫ y in productBox Q, |F.1 y|) / volume.real (productBox Q)) x) := by
  apply Finset.sup'_congr _ rfl
  intro Q _
  exact productAverageMap_univ_eq_integral Q (absoluteInput F) x

theorem finiteProductMaximal_nonneg
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A : Finset (Fin m)) (F : boundedMeasurableFunctions d) (x : ProductPoint d) :
    0 ≤ finiteProductMaximal I N A F x := by
  exact (product_average_nonneg (absoluteInput F) (fun y => abs_nonneg (F.1 y)) A I x).trans
    (Finset.le_sup' (fun Q => (productAverageMap A Q (absoluteInput F)).1 x)
      (root_mem_productDescendants I N))

theorem finiteProductMaximal_empty
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) :
    finiteProductMaximal I N ∅ F x = |F.1 x| := by
  apply Finset.sup'_eq_of_forall
  intro Q _
  simp [absoluteInput]

/-- A fixed product average is dominated by one occurrence of each selected
coordinate maximal function. The outer absolute value includes the empty list. -/
theorem productAverageMap_abs_le_iteratedMaximal
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (order : List (Fin m)) (horder : order.Nodup)
    (Q : ∀ i, Box (Fin (d i)))
    (hQ : ∀ i ∈ order, Q i ∈ descendants (I i) (N i))
    (x : ProductPoint d) (hx : x ∈ productBox I) :
    |(productAverageMap order.toFinset Q F).1 x| ≤
      |(order.foldr (fun i g => coordinateDyadicMaximal i (I i) (N i) g) F.1) x| := by
  revert horder hQ x
  induction order with
  | nil =>
    intro _ _ x _
    simp
  | cons j order ih =>
    intro horder hQ x hx
    have hj : j ∉ order.toFinset := by simpa using (List.nodup_cons.mp horder).1
    have htQ : ∀ i ∈ order, Q i ∈ descendants (I i) (N i) :=
      fun i hi => hQ i (List.mem_cons_of_mem j hi)
    let u := (productAverageMap order.toFinset Q F).1
    let v := order.foldr (fun i g => coordinateDyadicMaximal i (I i) (N i) g) F.1
    have hu : ProductLeafConstant I N u :=
      (productAverageMap_productStep_closure I N F hf hs order.toFinset Q
        (fun i hi => htQ i (List.mem_toFinset.mp hi))).1
    have hv : ProductLeafConstant I N v :=
      productLeafConstant_foldr_coordinateDyadicMaximal I N order F.1 hf
    have huv : ∀ y ∈ productBox I, |u y| ≤ |v y| :=
      fun y hy => ih (List.nodup_cons.mp horder).2 htQ y hy
    rw [List.toFinset_cons, productAverageMap_insert order.toFinset j hj Q,
      Module.End.mul_apply, averageMap_apply]
    calc
      _ ≤ coordinateDyadicMaximal j (I j) (N j) u x :=
        abs_coordinateAverage_le_coordinateDyadicMaximal u hu j (Q j)
          (hQ j List.mem_cons_self) x hx
      _ ≤ coordinateDyadicMaximal j (I j) (N j) v x :=
        coordinateDyadicMaximal_mono_abs u v hu hv huv j x hx
      _ = _ := (abs_of_nonneg (coordinateDyadicMaximal_nonneg j (I j) (N j) v x)).symm

theorem measurable_finiteProductMaximal
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A : Finset (Fin m)) (F : boundedMeasurableFunctions d) :
    Measurable (finiteProductMaximal I N A F) := by
  have h := Finset.measurable_sup' (s := productDescendants I N)
    ⟨I, root_mem_productDescendants I N⟩
    (fun Q _ => (productAverageMap A Q (absoluteInput F)).2.1)
  convert h using 1
  funext x
  exact (Finset.sup'_apply _ _ _).symm

theorem productLeafConstant_finiteProductMaximal
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A : Finset (Fin m)) (F : boundedMeasurableFunctions d)
    (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) :
    ProductLeafConstant I N (finiteProductMaximal I N A F) := by
  have hfabs : ProductLeafConstant I N (absoluteInput F).1 := by
    intro Q hQ x hx y hy
    exact congrArg abs (hf Q hQ x hx y hy)
  have hsabs : ∀ x, x ∉ productBox I → (absoluteInput F).1 x = 0 := by
    intro x hx
    change |F.1 x| = 0
    rw [hs x hx, abs_zero]
  intro P hP x hx y hy
  apply Finset.sup'_congr _ rfl
  intro Q hQ
  exact (productAverageMap_productStep_closure I N (absoluteInput F) hfabs hsabs A Q
    (fun i _ => mem_productDescendants.mp hQ i)).1 P hP x hx y hy

/-- The maximum itself, rather than a supplied upper bound, is dominated by
the iteration with each selected coordinate occurring exactly once. -/
theorem finiteProductMaximal_le_iterated
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A : Finset (Fin m)) (F : boundedMeasurableFunctions d)
    (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (x : ProductPoint d) (hx : x ∈ productBox I) :
    finiteProductMaximal I N A F x ≤
      |(A.toList.foldr (fun i g => coordinateDyadicMaximal i (I i) (N i) g)
        (fun y => |F.1 y|)) x| := by
  have hfabs : ProductLeafConstant I N (absoluteInput F).1 := by
    intro Q hQ y hy z hz
    exact congrArg abs (hf Q hQ y hy z hz)
  have hsabs : ∀ y, y ∉ productBox I → (absoluteInput F).1 y = 0 := by
    intro y hy
    change |F.1 y| = 0
    rw [hs y hy, abs_zero]
  apply Finset.sup'_le
  intro Q hQ
  have h := productAverageMap_abs_le_iteratedMaximal I N (absoluteInput F) hfabs hsabs
    A.toList A.nodup_toList Q (fun i _ => mem_productDescendants.mp hQ i) x hx
  rw [Finset.toList_toFinset,
    abs_of_nonneg (product_average_nonneg (absoluteInput F)
      (fun y => abs_nonneg (F.1 y)) A Q x)] at h
  exact h

private theorem integrableOn_product_leaf
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (g : ProductPoint d → ℝ) (hg : ProductLeafConstant I N g) :
    IntegrableOn g (productBox I) volume := by
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

/-- The finite product maximal estimate has exactly one ordinary maximal
factor for each selected coordinate, for every real exponent `p > 1`. -/
theorem finite_product_maximal_integral
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A : Finset (Fin m)) (hd : ∀ i ∈ A, 0 < d i)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (p : ℝ) (hp : 1 < p) :
    (∫ x in productBox I, Real.rpow (finiteProductMaximal I N A F x) p) ≤
      Real.rpow (p / (p - 1)) (p * (A.card : ℝ)) *
        ∫ x in productBox I, Real.rpow |F.1 x| p := by
  let g := A.toList.foldr (fun i h => coordinateDyadicMaximal i (I i) (N i) h)
    (fun x => |F.1 x|)
  have habs : ProductLeafConstant I N (fun x => |F.1 x|) := by
    intro Q hQ x hx y hy
    exact congrArg abs (hf Q hQ x hx y hy)
  have hg : ProductLeafConstant I N g :=
    productLeafConstant_foldr_coordinateDyadicMaximal I N A.toList _ habs
  have hM := productLeafConstant_finiteProductMaximal I N A F hf hs
  have hMI : IntegrableOn (fun x => Real.rpow (finiteProductMaximal I N A F x) p)
      (productBox I) volume := by
    apply integrableOn_product_leaf I N
    intro Q hQ x hx y hy
    dsimp only
    rw [hM Q hQ x hx y hy]
  have hgI : IntegrableOn (fun x => Real.rpow |g x| p) (productBox I) volume := by
    apply integrableOn_product_leaf I N
    intro Q hQ x hx y hy
    dsimp only
    rw [hg Q hQ x hx y hy]
  calc
    _ ≤ ∫ x in productBox I, Real.rpow |g x| p := by
      apply setIntegral_mono_on hMI hgI (measurableSet_productBox I)
      intro x hx
      exact Real.rpow_le_rpow (finiteProductMaximal_nonneg I N A F x)
        (finiteProductMaximal_le_iterated I N A F hf hs x hx) (by linarith)
    _ ≤ _ := by
      have h := finite_iterated_coordinate_maximal_integral I N A.toList
        (fun i hi => hd i (Finset.mem_toList.mp hi)) (fun x => |F.1 x|) habs p hp
      simpa only [Finset.length_toList, abs_abs] using h

end ReyZygmund
