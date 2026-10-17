import ReyZygmund.Geometry.ProductIntegrability
import ReyZygmund.Maximal.DiscreteLayerCake

/-! # Integrating the dyadic layer-cake comparison

For inputs constant on the smallest product cubes, finite indicator
representations give integrability and the measures of level sets on the top
rectangle. The exchanges involve finite sums and convergent series.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem integral_productLeafConstant_eq_sum
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f) :
    (∫ x in productRectangle I, f x) =
      ∑ Q ∈ productLeaves I N,
        volume.real (productRectangle Q) * f (fun i => (Q i).upper) := by
  rw [← integral_indicator (measurableSet_productRectangle I),
    product_step_representation I N f hf]
  simp only [Finset.sum_apply]
  rw [integral_finsetSum _ (fun Q _ =>
    (integrableOn_const (productRectangle_volume_lt_top Q).ne).integrable_indicator
      (measurableSet_productRectangle Q))]
  apply Finset.sum_congr rfl
  intro Q _
  rw [integral_indicator_const _ (measurableSet_productRectangle Q), smul_eq_mul]

private theorem measurableSet_product_superlevel
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (H : ProductPoint d → ℝ) (hH : ProductLeafConstant I N H) (r : ℝ) :
    MeasurableSet {x | x ∈ productRectangle I ∧ r < H x} := by
  have heq : {x | x ∈ productRectangle I ∧ r < H x} =
      productRectangle I ∩ {x | r < (productRectangle I).indicator H x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    by_cases hx : x ∈ productRectangle I
    · rw [Set.indicator_of_mem hx]
    · simp only [hx, false_and]
  rw [heq]
  exact (measurableSet_productRectangle I).inter
    (measurableSet_lt measurable_const (measurable_product_localization I N H hH))

private theorem volume_product_superlevel_eq_sum
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (H : ProductPoint d → ℝ) (hH : ProductLeafConstant I N H) (r : ℝ) :
    volume.real {x | x ∈ productRectangle I ∧ r < H x} =
      ∑ Q ∈ productLeaves I N, volume.real (productRectangle Q) *
        (if r < H (fun i => (Q i).upper) then 1 else 0) := by
  have hf : ProductLeafConstant I N (fun x => if r < H x then (1 : ℝ) else 0) := by
    intro Q hQ x hx y hy
    dsimp only
    rw [hH Q hQ x hx y hy]
  have heq : (productRectangle I).indicator (fun x => if r < H x then (1 : ℝ) else 0) =
      {x | x ∈ productRectangle I ∧ r < H x}.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ productRectangle I
    · rw [Set.indicator_of_mem hx]
      by_cases hr : r < H x
      · rw [ite_eq_left hr, Set.indicator_of_mem
          (show x ∈ {x | x ∈ productRectangle I ∧ r < H x} from ⟨hx, hr⟩)]
      · rw [ite_eq_right hr, Set.indicator_of_notMem
          (show x ∉ {x | x ∈ productRectangle I ∧ r < H x} from fun h => hr h.2)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem
        (show x ∉ {x | x ∈ productRectangle I ∧ r < H x} from fun h => hx h.1)]
  have hi := integral_productLeafConstant_eq_sum I N _ hf
  rw [← integral_indicator (measurableSet_productRectangle I), heq,
    integral_indicator_const _ (measurableSet_product_superlevel I N H hH r)] at hi
  simpa only [smul_eq_mul, mul_one] using hi

private theorem hasSum_dyadic_layerCake_integral
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (H : ProductPoint d → ℝ) (hH : ProductLeafConstant I N H)
    (hH0 : ∀ x ∈ productRectangle I, 0 ≤ H x) (p : ℝ) (hp : 0 < p) :
    HasSum (fun n : ℤ => Real.rpow 2 (p * (n : ℝ)) *
      volume.real {x | x ∈ productRectangle I ∧ Real.rpow 2 (n : ℝ) < H x})
      (∑ Q ∈ productLeaves I N, volume.real (productRectangle Q) *
        ∑' n : ℤ, if Real.rpow 2 (n : ℝ) < H (fun i => (Q i).upper) then
          Real.rpow 2 (p * (n : ℝ)) else 0) := by
  have hs : HasSum
      (fun n : ℤ => ∑ Q ∈ productLeaves I N, volume.real (productRectangle Q) *
        (if Real.rpow 2 (n : ℝ) < H (fun i => (Q i).upper) then
          Real.rpow 2 (p * (n : ℝ)) else 0))
      (∑ Q ∈ productLeaves I N, volume.real (productRectangle Q) *
        ∑' n : ℤ, if Real.rpow 2 (n : ℝ) < H (fun i => (Q i).upper) then
          Real.rpow 2 (p * (n : ℝ)) else 0) := by
    apply hasSum_sum
    intro Q hQ
    have h0 : 0 ≤ H (fun i => (Q i).upper) :=
      hH0 _ (productLeaves_subset hQ
        ((mem_productRectangle Q _).mpr (fun i => (Q i).upper_mem)))
    exact (summable_dyadic_layerCake _ p h0 hp).hasSum.mul_left _
  apply hs.congr_fun
  intro n
  rw [volume_product_superlevel_eq_sum I N H hH, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q _
  by_cases h : Real.rpow 2 (n : ℝ) < H (fun i => (Q i).upper)
  · simp only [ite_eq_left h, mul_one]
    ring
  · simp only [ite_eq_right h, mul_zero]

/-- For an input nonnegative on the top rectangle and constant on its smallest cubes,
the superlevel-volume series converges for every positive exponent. -/
theorem summable_dyadic_layerCake_integral
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (H : ProductPoint d → ℝ) (hH : ProductLeafConstant I N H)
    (hH0 : ∀ x ∈ productRectangle I, 0 ≤ H x) (p : ℝ) (hp : 0 < p) :
    Summable (fun n : ℤ => Real.rpow 2 (p * (n : ℝ)) *
      volume.real {x | x ∈ productRectangle I ∧ Real.rpow 2 (n : ℝ) < H x}) :=
  (hasSum_dyadic_layerCake_integral I N H hH hH0 p hp).summable

/-- The integrated comparison uses strict dyadic thresholds and restricted Lebesgue
integrals on the top rectangle. -/
theorem dyadic_layerCake_integral_bounds
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (H : ProductPoint d → ℝ) (hH : ProductLeafConstant I N H)
    (hH0 : ∀ x ∈ productRectangle I, 0 ≤ H x) (p : ℝ)
    (hp : 1 ≤ p) (hp3 : p ≤ (3 : ℝ) / 2) :
    (∫ x in productRectangle I, Real.rpow (H x) p) / 4 ≤
        (∑' n : ℤ, Real.rpow 2 (p * (n : ℝ)) *
          volume.real {x | x ∈ productRectangle I ∧ Real.rpow 2 (n : ℝ) < H x}) ∧
      (∑' n : ℤ, Real.rpow 2 (p * (n : ℝ)) *
          volume.real {x | x ∈ productRectangle I ∧ Real.rpow 2 (n : ℝ) < H x}) ≤
        2 * (∫ x in productRectangle I, Real.rpow (H x) p) := by
  have hs := hasSum_dyadic_layerCake_integral I N H hH hH0 p (zero_lt_one.trans_le hp)
  have hpower : ProductLeafConstant I N (fun x => Real.rpow (H x) p) := by
    intro Q hQ x hx y hy
    exact congrArg (fun t => Real.rpow t p) (hH Q hQ x hx y hy)
  rw [hs.tsum_eq, integral_productLeafConstant_eq_sum I N _ hpower]
  constructor
  · calc
      (∑ Q ∈ productLeaves I N, volume.real (productRectangle Q) *
          Real.rpow (H (fun i => (Q i).upper)) p) / 4 =
          ∑ Q ∈ productLeaves I N, volume.real (productRectangle Q) *
            (Real.rpow (H (fun i => (Q i).upper)) p / 4) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro Q _
        ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro Q hQ
        have h0 : 0 ≤ H (fun i => (Q i).upper) :=
          hH0 _ (productLeaves_subset hQ
            ((mem_productRectangle Q _).mpr (fun i => (Q i).upper_mem)))
        exact mul_le_mul_of_nonneg_left (dyadic_layerCake_bounds _ p h0 hp hp3).1
          measureReal_nonneg
  · calc
      _ ≤ ∑ Q ∈ productLeaves I N, volume.real (productRectangle Q) *
          (2 * Real.rpow (H (fun i => (Q i).upper)) p) := by
        apply Finset.sum_le_sum
        intro Q hQ
        have h0 : 0 ≤ H (fun i => (Q i).upper) :=
          hH0 _ (productLeaves_subset hQ
            ((mem_productRectangle Q _).mpr (fun i => (Q i).upper_mem)))
        exact mul_le_mul_of_nonneg_left (dyadic_layerCake_bounds _ p h0 hp hp3).2
          measureReal_nonneg
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro Q _
        ring

end ReyZygmund
