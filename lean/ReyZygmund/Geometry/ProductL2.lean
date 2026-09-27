import ReyZygmund.Geometry.ProductMean
import ReyZygmund.Geometry.ProductOrthogonality
import ReyZygmund.Projection.FiniteIndices

/-! # L² orthogonality of product differences

Lebesgue integration makes coordinate averages self-adjoint. Combined with the
algebraic cancellation identities, this gives orthogonality of product
differences. For signed bounded measurable inputs, the products and finite squares
are integrable on the top rectangle.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private noncomputable def boundedMul (F G : boundedMeasurableFunctions d) :
    boundedMeasurableFunctions d :=
  ⟨fun x => F.1 x * G.1 x, F.2.1.mul G.2.1, by
    obtain ⟨C, hC, hF⟩ := F.2.2
    obtain ⟨D, hD, hG⟩ := G.2.2
    refine ⟨C * D, mul_nonneg hC hD, ?_⟩
    intro x
    rw [abs_mul]
    exact mul_le_mul (hF x) (hG x) (abs_nonneg _) hC⟩

private theorem boundedMul_apply (F G : boundedMeasurableFunctions d) (x : ProductPoint d) :
    (boundedMul F G).1 x = F.1 x * G.1 x := rfl

private theorem productBox_volume_pos (I : ∀ i, Box (Fin (d i))) :
    0 < volume.real (productBox I) := by
  change 0 < (Measure.pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
    (Set.pi Set.univ (fun i => (I i : Set (Fin (d i) → ℝ))))).toReal
  rw [Measure.pi_pi, ENNReal.toReal_prod]
  exact Finset.prod_pos (fun i _ => box_volume_pos (I i))

private theorem integrableOn_bounded (I : ∀ i, Box (Fin (d i)))
    (F : boundedMeasurableFunctions d) : IntegrableOn F.1 (productBox I) volume := by
  have hvol : volume (productBox I) < ∞ := by
    change Measure.pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
      (Set.pi Set.univ (fun i => (I i : Set (Fin (d i) → ℝ)))) < ∞
    rw [Measure.pi_pi]
    exact ENNReal.prod_lt_top (fun i _ => (I i).measure_coe_lt_top volume)
  let : IsFiniteMeasure (volume.restrict (productBox I)) :=
    isFiniteMeasure_restrict.mpr hvol.ne
  obtain ⟨C, _, hC⟩ := F.2.2
  exact (integrable_const C).mono' F.2.1.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using hC x))

private theorem integrableOn_mul (I : ∀ i, Box (Fin (d i)))
    (F G : boundedMeasurableFunctions d) :
    IntegrableOn (fun x => F.1 x * G.1 x) (productBox I) volume :=
  integrableOn_bounded I (boundedMul F G)

private theorem boxAverage_mul_integral {k : ℕ} (I Q : Box (Fin k)) (hQI : Q ≤ I)
    (f g : (Fin k → ℝ) → ℝ) :
    (∫ x in (I : Set (Fin k → ℝ)), boxAverage Q f x * g x) =
      ((∫ x in (Q : Set (Fin k → ℝ)), f x) / volume.real (Q : Set (Fin k → ℝ))) *
        ∫ x in (Q : Set (Fin k → ℝ)), g x := by
  calc
    _ = ∫ x in (Q : Set (Fin k → ℝ)), boxAverage Q f x * g x := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero I.measurableSet_coe hQI
      intro x hx
      rw [DifferenceAlgebra.boxAverage_eq_zero_of_notMem Q f hx.2, zero_mul]
    _ = ∫ x in (Q : Set (Fin k → ℝ)),
        ((∫ y in (Q : Set (Fin k → ℝ)), f y) / volume.real (Q : Set (Fin k → ℝ))) *
          g x := by
      apply setIntegral_congr_fun Q.measurableSet_coe
      intro x hx
      change boxAverage Q f x * g x = _
      simp only [boxAverage, Set.indicator_of_mem hx]
    _ = _ := integral_const_mul _ _

private theorem boxAverage_pairing {k : ℕ} (I Q : Box (Fin k)) (hQI : Q ≤ I)
    (f g : (Fin k → ℝ) → ℝ) :
    (∫ x in (I : Set (Fin k → ℝ)), boxAverage Q f x * g x) =
      ∫ x in (I : Set (Fin k → ℝ)), f x * boxAverage Q g x := by
  calc
    _ = ((∫ x in (Q : Set (Fin k → ℝ)), f x) /
        volume.real (Q : Set (Fin k → ℝ))) * ∫ x in (Q : Set (Fin k → ℝ)), g x :=
      boxAverage_mul_integral I Q hQI f g
    _ = ((∫ x in (Q : Set (Fin k → ℝ)), g x) /
        volume.real (Q : Set (Fin k → ℝ))) * ∫ x in (Q : Set (Fin k → ℝ)), f x := by ring
    _ = ∫ x in (I : Set (Fin k → ℝ)), boxAverage Q g x * f x :=
      (boxAverage_mul_integral I Q hQI g f).symm
    _ = _ := by
      apply setIntegral_congr_fun I.measurableSet_coe
      intro x _
      exact mul_comm _ _

private theorem coordinateAverage_pairing (j : Fin m)
    (I Q : Box (Fin (d j))) (hQI : Q ≤ I) (f g : ProductPoint d → ℝ) :
    coordinateAverage j I (fun x => coordinateAverage j Q f x * g x) =
      coordinateAverage j I (fun x => f x * coordinateAverage j Q g x) := by
  funext x
  by_cases hx : x j ∈ I
  · rw [coordinateAverage_of_mem j I _ x hx, coordinateAverage_of_mem j I _ x hx]
    apply congrArg (fun a : ℝ => a / volume.real (I : Set (Fin (d j) → ℝ)))
    simpa only [coordinateAverage, Function.update_self, Function.update_idem] using
      boxAverage_pairing I Q hQI (fun y => f (Function.update x j y))
        (fun y => g (Function.update x j y))
  · rw [coordinateAverage_of_notMem j I _ x hx, coordinateAverage_of_notMem j I _ x hx]

private theorem integral_eq_of_averageMap_eq (I : ∀ i, Box (Fin (d i)))
    (j : Fin m) (F G : boundedMeasurableFunctions d)
    (h : averageMap j (I j) F = averageMap j (I j) G) :
    (∫ x in productBox I, F.1 x) = ∫ x in productBox I, G.1 x := by
  have hop : productAverageMap Finset.univ I =
      productAverageMap (Finset.univ.erase j) I * averageMap j (I j) := by
    symm
    exact Finset.noncommProd_erase_mul Finset.univ (Finset.mem_univ j)
      (fun i => averageMap i (I i))
      (fun i _ k _ hik => averageMap_commute i k hik (I i) (I k))
  have hfull : productAverageMap Finset.univ I F = productAverageMap Finset.univ I G := by
    rw [hop, Module.End.mul_apply, Module.End.mul_apply, h]
  have hx : (fun i => (I i).upper) ∈ productBox I :=
    (mem_productBox I _).mpr (fun i => (I i).upper_mem)
  have hmean := congrArg (fun H : boundedMeasurableFunctions d => H.1 (fun i => (I i).upper)) hfull
  simp only [productAverageMap_univ_eq_integral, Set.indicator_of_mem hx] at hmean
  exact (div_left_inj' (ne_of_gt (productBox_volume_pos I))).mp hmean

private theorem averageMap_integral_pairing (I : ∀ i, Box (Fin (d i)))
    (j : Fin m) (Q : Box (Fin (d j))) (hQI : Q ≤ I j)
    (F G : boundedMeasurableFunctions d) :
    (∫ x in productBox I, (averageMap j Q F).1 x * G.1 x) =
      ∫ x in productBox I, F.1 x * (averageMap j Q G).1 x := by
  apply integral_eq_of_averageMap_eq I j
    (boundedMul (averageMap j Q F) G) (boundedMul F (averageMap j Q G))
  apply Subtype.ext
  simpa only [averageMap_apply, boundedMul] using
    coordinateAverage_pairing j (I j) Q hQI F.1 G.1

private noncomputable def pairing (I : ∀ i, Box (Fin (d i)))
    (F G : boundedMeasurableFunctions d) : ℝ :=
  ∫ x in productBox I, F.1 x * G.1 x

private theorem pairing_comm (I : ∀ i, Box (Fin (d i)))
    (F G : boundedMeasurableFunctions d) : pairing I F G = pairing I G F := by
  apply setIntegral_congr_fun (measurableSet_productBox I)
  intro x _
  exact mul_comm _ _

private theorem pairing_add_left (I : ∀ i, Box (Fin (d i)))
    (F G H : boundedMeasurableFunctions d) :
    pairing I (F + G) H = pairing I F H + pairing I G H := by
  change (∫ x in productBox I, (F.1 x + G.1 x) * H.1 x) = _
  simp_rw [add_mul]
  exact integral_add (integrableOn_mul I F H) (integrableOn_mul I G H)

private theorem pairing_sub_left (I : ∀ i, Box (Fin (d i)))
    (F G H : boundedMeasurableFunctions d) :
    pairing I (F - G) H = pairing I F H - pairing I G H := by
  change (∫ x in productBox I, (F.1 x - G.1 x) * H.1 x) = _
  simp_rw [sub_mul]
  exact integral_sub (integrableOn_mul I F H) (integrableOn_mul I G H)

private theorem pairing_sub_right (I : ∀ i, Box (Fin (d i)))
    (F G H : boundedMeasurableFunctions d) :
    pairing I F (G - H) = pairing I F G - pairing I F H := by
  calc
    _ = pairing I (G - H) F := pairing_comm I F (G - H)
    _ = pairing I G F - pairing I H F := pairing_sub_left I G H F
    _ = _ := by rw [pairing_comm I G F, pairing_comm I H F]

private theorem pairing_sum_left {α : Type*} (I : ∀ i, Box (Fin (d i)))
    (S : Finset α) (F : α → boundedMeasurableFunctions d) (G : boundedMeasurableFunctions d) :
    pairing I (∑ a ∈ S, F a) G = ∑ a ∈ S, pairing I (F a) G := by
  induction S using Finset.induction_on with
  | empty => simp [pairing]
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, pairing_add_left, ih, Finset.sum_insert ha]

private theorem pairing_sum_right {α : Type*} (I : ∀ i, Box (Fin (d i)))
    (S : Finset α) (F : boundedMeasurableFunctions d) (G : α → boundedMeasurableFunctions d) :
    pairing I F (∑ a ∈ S, G a) = ∑ a ∈ S, pairing I F (G a) := by
  rw [pairing_comm, pairing_sum_left]
  exact Finset.sum_congr rfl (fun a _ => pairing_comm I (G a) F)

private theorem differenceMap_integral_pairing (I : ∀ i, Box (Fin (d i)))
    (j : Fin m) (Q : Box (Fin (d j))) (hQI : Q ≤ I j)
    (F G : boundedMeasurableFunctions d) :
    pairing I (differenceMap j Q F) G = pairing I F (differenceMap j Q G) := by
  simp only [differenceMap, LinearMap.sub_apply, LinearMap.sum_apply]
  rw [pairing_sub_left, pairing_sum_left, pairing_sub_right, pairing_sum_right]
  congr 1
  · apply Finset.sum_congr rfl
    intro R hR
    exact averageMap_integral_pairing I j R
      (((Prepartition.splitCenter Q).le_of_mem hR).trans hQI) F G
  · exact averageMap_integral_pairing I j Q hQI F G

/-- Distinct full product differences are orthogonal on the top rectangle, by
self-adjointness of averages and dyadic cancellation. -/
theorem productDifference_integral_mul_eq_zero
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (F : boundedMeasurableFunctions d) (L Q : ∀ i, Box (Fin (d i)))
    (hL : L ∈ Projection.productInterior I N) (hQ : Q ∈ Projection.productInterior I N)
    (hne : L ≠ Q) :
    (∫ x in productBox I, (productDifferenceMap Finset.univ L F).1 x *
      (productDifferenceMap Finset.univ Q F).1 x) = 0 := by
  have hex : ∃ i, L i ≠ Q i := by
    by_contra h
    apply hne
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  have hLi : L i ∈ descendants (I i) (N i) :=
    interior_subset_descendants (I i) (N i) (Projection.mem_productInterior.mp hL i)
  have hQi : Q i ∈ descendants (I i) (N i) :=
    interior_subset_descendants (I i) (N i) (Projection.mem_productInterior.mp hQ i)
  have hfix : differenceMap i (L i) (productDifferenceMap Finset.univ L F) =
      productDifferenceMap Finset.univ L F := by
    have hop := differenceMap_mul_productDifferenceMap I N Finset.univ i
      (Finset.mem_univ i) (hd i) (L i) L hLi hLi
    rw [ite_eq_left rfl] at hop
    simpa only [Module.End.mul_apply] using
      congrArg (fun T : Module.End ℝ (boundedMeasurableFunctions d) => T F) hop
  have hzero : differenceMap i (L i) (productDifferenceMap Finset.univ Q F) = 0 := by
    have hop := differenceMap_mul_productDifferenceMap I N Finset.univ i
      (Finset.mem_univ i) (hd i) (L i) Q hLi hQi
    rw [ite_eq_right hi] at hop
    simpa only [Module.End.mul_apply, LinearMap.zero_apply] using
      congrArg (fun T : Module.End ℝ (boundedMeasurableFunctions d) => T F) hop
  change pairing I (productDifferenceMap Finset.univ L F) (productDifferenceMap Finset.univ Q F) = 0
  calc
    _ = pairing I (differenceMap i (L i) (productDifferenceMap Finset.univ L F))
        (productDifferenceMap Finset.univ Q F) := by rw [hfix]
    _ = pairing I (productDifferenceMap Finset.univ L F)
        (differenceMap i (L i) (productDifferenceMap Finset.univ Q F)) :=
      differenceMap_integral_pairing I i (L i) (le_of_mem_descendants hLi) _ _
    _ = 0 := by rw [hzero]; simp [pairing]

private theorem boundedSum_apply {α : Type*} (S : Finset α)
    (F : α → boundedMeasurableFunctions d) (x : ProductPoint d) :
    (∑ a ∈ S, F a).1 x = ∑ a ∈ S, (F a).1 x := by
  induction S using Finset.induction_on with
  | empty => rfl
  | @insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    change (F a).1 x + (∑ a ∈ S, F a).1 x = (F a).1 x + ∑ a ∈ S, (F a).1 x
    rw [ih]

private theorem integrableOn_sum_sq {α : Type*} (I : ∀ i, Box (Fin (d i)))
    (S : Finset α) (F : α → boundedMeasurableFunctions d) :
    IntegrableOn (fun x => (∑ a ∈ S, (F a).1 x) ^ 2) (productBox I) volume := by
  simpa only [boundedSum_apply, pow_two] using
    integrableOn_mul I (∑ a ∈ S, F a) (∑ a ∈ S, F a)

/-- Exact finite-sum square identity on the top rectangle. In particular,
the empty family is allowed, and the input need not be nonnegative. -/
theorem productDifference_integral_sum_sq
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (F : boundedMeasurableFunctions d) (H : Finset (∀ i, Box (Fin (d i))))
    (hH : H ⊆ Projection.productInterior I N) :
    (∫ x in productBox I, (∑ Q ∈ H, (productDifferenceMap Finset.univ Q F).1 x) ^ 2) =
      ∑ Q ∈ H, ∫ x in productBox I, ((productDifferenceMap Finset.univ Q F).1 x) ^ 2 := by
  let U := fun Q : ∀ i, Box (Fin (d i)) => productDifferenceMap Finset.univ Q F
  calc
    (∫ x in productBox I, (∑ Q ∈ H, (U Q).1 x) ^ 2) =
        pairing I (∑ Q ∈ H, U Q) (∑ Q ∈ H, U Q) := by
      apply setIntegral_congr_fun (measurableSet_productBox I)
      intro x _
      simp only [boundedSum_apply, pow_two]
    _ = ∑ Q ∈ H, ∑ L ∈ H, pairing I (U Q) (U L) := by
      rw [pairing_sum_left]
      exact Finset.sum_congr rfl (fun Q _ => pairing_sum_right I H (U Q) U)
    _ = ∑ Q ∈ H, ∫ x in productBox I, ((U Q).1 x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro Q hQ
      rw [Finset.sum_eq_single Q]
      · simp only [pairing, pow_two]
      · intro L hL hLQ
        exact productDifference_integral_mul_eq_zero I N hd F Q L (hH hQ) (hH hL) hLQ.symm
      · intro hnot
        exact (hnot hQ).elim

end ReyZygmund.Geometry
