import ReyZygmund.Weighted.ProductStep
import ReyZygmund.Geometry.PartialIndices

/-! # The finite product square-function estimate

Count each tuple of selected interior cubes once, fixing other coordinates at the
top cubes. Support identifies the integrals on the top rectangle with the cylinder
integrals in the paper, with the same product constant.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem productAverage_congr (A : Finset (Fin m))
    (K L : ∀ i, Box (Fin (d i))) (h : ∀ i ∈ A, K i = L i) :
    productAverageMap A K = productAverageMap A L := by
  apply Finset.noncommProd_congr rfl
  intro i hi
  rw [h i hi]

private theorem productDifference_insert_update (A : Finset (Fin m))
    (j : Fin m) (hj : j ∉ A) (Q : ∀ i, Box (Fin (d i))) (R : Box (Fin (d j))) :
    productDifferenceMap (insert j A) (Function.update Q j R) =
      differenceMap j R * productDifferenceMap A Q := by
  have heq : ∀ i ∈ A, (Function.update Q j R) i = Q i := by
    intro i hi
    have hij : i ≠ j := by
      intro h
      subst i
      exact hj hi
    exact Function.update_of_ne hij R Q
  rw [productDifferenceMap_insert A j hj, Function.update_self,
    productDifferenceMap_congr A _ Q heq]

private theorem productAverage_insert_update (A : Finset (Fin m))
    (j : Fin m) (hj : j ∉ A) (Q : ∀ i, Box (Fin (d i))) (R : Box (Fin (d j))) :
    productAverageMap (insert j A) (Function.update Q j R) =
      averageMap j R * productAverageMap A Q := by
  have heq : ∀ i ∈ A, (Function.update Q j R) i = Q i := by
    intro i hi
    have hij : i ≠ j := by
      intro h
      subst i
      exact hj hi
    exact Function.update_of_ne hij R Q
  rw [productAverageMap_insert A j hj, Function.update_self,
    productAverage_congr A _ Q heq]

private theorem product_difference_zero_off_selected (A : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) (F : boundedMeasurableFunctions d)
    (x : ProductPoint d) (hx : ¬ ∀ i ∈ A, x i ∈ Q i) :
    (productDifferenceMap A Q F).1 x = 0 := by
  push Not at hx
  obtain ⟨i, hi, hxi⟩ := hx
  rw [productDifferenceMap_eq_mul_erase A i hi Q]
  simp only [Module.End.mul_apply, differenceMap_apply, coordinateDifference_slice]
  exact DifferenceAlgebra.boxDifference_eq_zero_of_notMem (Q i) _ hxi

private theorem partialInterior_productBox_subset
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A : Finset (Fin m)) (Q : ∀ i, Box (Fin (d i)))
    (hQ : Q ∈ partialInterior I N A) : productBox Q ⊆ productBox I := by
  intro x hx
  apply (mem_productBox I x).mpr
  intro i
  by_cases hi : i ∈ A
  · exact le_of_mem_descendants
      (interior_subset_descendants (I i) (N i) (partialInterior_mem_selected hQ hi))
      ((mem_productBox Q x).mp hx i)
  · simpa only [partialInterior_mem_unselected hQ hi] using
      (mem_productBox Q x).mp hx i

private theorem integrableOn_product_leaf (I : ∀ i, Box (Fin (d i)))
    (N : Fin m → ℕ) (g : ProductPoint d → ℝ) (hg : ProductLeafConstant I N g) :
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

private theorem product_energy_integrable
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (A : Finset (Fin m)) (Q : ∀ i, Box (Fin (d i)))
    (hQ : Q ∈ partialInterior I N A) (p : ℝ) :
    let F := finiteInput I N f hf
    let g := fun x => ((productDifferenceMap A Q F).1 x) ^ 2 /
      Real.rpow ((productAverageMap A Q F).1 x) (2 - p)
    IntegrableOn g (productBox I) volume ∧ IntegrableOn g (productBox Q) volume := by
  let F := finiteInput I N f hf
  have hF : ProductLeafConstant I N F.1 := productLeafConstant_indicator hf
  have hFs : ∀ x, x ∉ productBox I → F.1 x = 0 :=
    fun x hx => Set.indicator_of_notMem hx f
  have hQi : ∀ i ∈ A, Q i ∈ interior (I i) (N i) :=
    fun i hi => partialInterior_mem_selected hQ hi
  have hu := (productDifferenceMap_productStep_closure I N F hF hFs A Q hQi).1
  have hv := (productAverageMap_productStep_closure I N F hF hFs A Q
    (fun i hi => interior_subset_descendants (I i) (N i) (hQi i hi))).1
  have hg : ProductLeafConstant I N (fun x =>
      ((productDifferenceMap A Q F).1 x) ^ 2 /
        Real.rpow ((productAverageMap A Q F).1 x) (2 - p)) := by
    intro P hP x hx y hy
    dsimp only
    rw [hu P hP x hx y hy, hv P hP x hx y hy]
  have hInt := integrableOn_product_leaf I N _ hg
  exact ⟨hInt, hInt.mono_set (partialInterior_productBox_subset I N A Q hQ)⟩

private theorem product_energy_average_pos
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productBox I, 0 < f x)
    (A : Finset (Fin m)) (Q : ∀ i, Box (Fin (d i)))
    (hQ : Q ∈ partialInterior I N A) (x : ProductPoint d) (hx : x ∈ productBox Q) :
    0 < (productAverageMap A Q (finiteInput I N f hf)).1 x := by
  have hFpos : ∀ y ∈ productBox I, 0 < (finiteInput I N f hf).1 y := by
    intro y hy
    change 0 < (productBox I).indicator f y
    rw [Set.indicator_of_mem hy]
    exact hfpos y hy
  exact productAverageMap_pos I (finiteInput I N f hf) hFpos A Q
    (fun i hi => le_of_mem_descendants
      (interior_subset_descendants (I i) (N i) (partialInterior_mem_selected hQ hi)))
    x (partialInterior_productBox_subset I N A Q hQ hx)
    (fun i _ => (mem_productBox Q x).mp hx i)

private theorem product_power_integrable
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f) (p : ℝ) :
    IntegrableOn (fun x => Real.rpow (f x) p) (productBox I) volume := by
  apply integrableOn_product_leaf I N
  intro P hP x hx y hy
  dsimp only
  rw [hf P hP x hx y hy]

/-- Support equates the energy integral on the top rectangle with the cylinder
integral for each partial index, for every real exponent. -/
theorem product_energy_integral_cylinder
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (A : Finset (Fin m)) (Q : ∀ i, Box (Fin (d i)))
    (hQ : Q ∈ partialInterior I N A) (p : ℝ) :
    let F := finiteInput I N f hf
    (∫ x in productBox I, ((productDifferenceMap A Q F).1 x) ^ 2 /
      Real.rpow ((productAverageMap A Q F).1 x) (2 - p)) =
    ∫ x in productBox Q, ((productDifferenceMap A Q F).1 x) ^ 2 /
      Real.rpow ((productAverageMap A Q F).1 x) (2 - p) := by
  let F := finiteInput I N f hf
  have hsub := partialInterior_productBox_subset I N A Q hQ
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_productBox I) hsub
  intro x hx
  have hnot : ¬ ∀ i ∈ A, x i ∈ Q i := by
    intro hsel
    apply hx.2
    apply (mem_productBox Q x).mpr
    intro i
    by_cases hi : i ∈ A
    · exact hsel i hi
    · rw [partialInterior_mem_unselected hQ hi]
      exact (mem_productBox I x).mp hx.1 i
  change ((productDifferenceMap A Q F).1 x) ^ 2 /
    Real.rpow ((productAverageMap A Q F).1 x) (2 - p) = 0
  rw [product_difference_zero_off_selected A Q F x hnot]
  simp

private theorem base_energy (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productBox I, 0 < f x) (p : ℝ) :
    (∫ x in productBox I, ((finiteInput I N f hf).1 x) ^ 2 /
      Real.rpow ((finiteInput I N f hf).1 x) (2 - p)) =
    ∫ x in productBox I, Real.rpow (f x) p := by
  apply setIntegral_congr_fun (measurableSet_productBox I)
  intro x hx
  change ((productBox I).indicator f x) ^ 2 /
    Real.rpow ((productBox I).indicator f x) (2 - p) = Real.rpow (f x) p
  rw [Set.indicator_of_mem hx]
  calc
    _ = Real.rpow (f x) 2 / Real.rpow (f x) (2 - p) := by
      simp only [Real.rpow_eq_pow, Real.rpow_two]
    _ = Real.rpow (f x) (2 - (2 - p)) := (Real.rpow_sub (hfpos x hx) 2 (2 - p)).symm
    _ = Real.rpow (f x) p := by congr 1; ring

private theorem product_square_constant (A : Finset (Fin m)) (p : ℝ) :
    (∏ i ∈ A, Real.rpow 2 ((d i : ℝ) * (2 - p)) * ((3 - p) / (p - 1))) =
      Real.rpow 2 ((2 - p) * (∑ i ∈ A, (d i : ℝ))) *
        ((3 - p) / (p - 1)) ^ A.card := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert j A hj ih =>
    rw [Finset.prod_insert hj, ih, Finset.sum_insert hj,
      Finset.card_insert_of_notMem hj, pow_succ, mul_add]
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), mul_comm (d j : ℝ) (2 - p)]
    ring

/-- The finite product square estimate, with the empty selected set
included as its equality base. Every summand is supported on its source
cylinder, as recorded in `product_energy_integral_cylinder`. -/
theorem product_weighted_square
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productBox I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2)
    (A : Finset (Fin m)) (hd : ∀ i ∈ A, 0 < d i) :
    let F := finiteInput I N f hf
    (∑ Q ∈ partialInterior I N A, ∫ x in productBox I,
      ((productDifferenceMap A Q F).1 x) ^ 2 /
        Real.rpow ((productAverageMap A Q F).1 x) (2 - p)) ≤
      Real.rpow 2 ((2 - p) * (∑ i ∈ A, (d i : ℝ))) *
        ((3 - p) / (p - 1)) ^ A.card *
          ∫ x in productBox I, Real.rpow (f x) p := by
  let F := finiteInput I N f hf
  let E (B : Finset (Fin m)) (Q : ∀ i, Box (Fin (d i))) :=
    ∫ x in productBox I, ((productDifferenceMap B Q F).1 x) ^ 2 /
      Real.rpow ((productAverageMap B Q F).1 x) (2 - p)
  let c (i : Fin m) := Real.rpow 2 ((d i : ℝ) * (2 - p)) * ((3 - p) / (p - 1))
  have hbound : ∀ B : Finset (Fin m), (∀ i ∈ B, 0 < d i) →
      (∑ Q ∈ partialInterior I N B, E B Q) ≤
        (∏ i ∈ B, c i) * ∫ x in productBox I, Real.rpow (f x) p := by
    intro B
    induction B using Finset.induction_on with
    | empty =>
      intro _
      simp only [partialInterior_empty, Finset.sum_singleton, Finset.prod_empty, one_mul]
      dsimp only [E]
      simp only [productDifferenceMap_empty, productAverageMap_empty, Module.End.one_apply]
      exact (base_energy I N f hf hfpos p).le
    | @insert j B hj ih =>
      intro hB
      have hBj : ∀ i ∈ B, 0 < d i := fun i hi => hB i (Finset.mem_insert_of_mem hi)
      have hc : 0 ≤ c j := by
        exact mul_nonneg (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
          (div_nonneg (by linarith) (by linarith))
      rw [sum_partialInterior_insert I N B j hj, Finset.sum_comm]
      calc
        (∑ Q ∈ partialInterior I N B, ∑ R ∈ interior (I j) (N j),
            E (insert j B) (Function.update Q j R)) =
            ∑ Q ∈ partialInterior I N B, ∑ R ∈ interior (I j) (N j),
              ∫ x in productBox I,
                (coordinateDifference j R (productDifferenceMap B Q F).1 x) ^ 2 /
                  Real.rpow (coordinateAverage j R (productAverageMap B Q F).1 x) (2 - p) := by
          apply Finset.sum_congr rfl
          intro Q _
          apply Finset.sum_congr rfl
          intro R _
          simp only [E, productDifference_insert_update B j hj,
            productAverage_insert_update B j hj, Module.End.mul_apply,
            differenceMap_apply, averageMap_apply]
        _ ≤ ∑ Q ∈ partialInterior I N B, c j * E B Q := by
          apply Finset.sum_le_sum
          intro Q hQ
          exact weighted_product_step I N f hf hfpos p hp hp2 B j hj
            (hB j (Finset.mem_insert_self j B)) Q
            (fun i hi => partialInterior_mem_selected hQ hi)
        _ = c j * ∑ Q ∈ partialInterior I N B, E B Q := by rw [Finset.mul_sum]
        _ ≤ c j * ((∏ i ∈ B, c i) * ∫ x in productBox I, Real.rpow (f x) p) :=
          mul_le_mul_of_nonneg_left (ih hBj) hc
        _ = (∏ i ∈ insert j B, c i) * ∫ x in productBox I, Real.rpow (f x) p := by
          rw [Finset.prod_insert hj]
          ring
  have h := hbound A hd
  dsimp only [c] at h
  rw [product_square_constant A p] at h
  exact h

end ReyZygmund
