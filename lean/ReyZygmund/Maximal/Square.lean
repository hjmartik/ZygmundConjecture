import ReyZygmund.Maximal.SquareDistribution
import ReyZygmund.Maximal.DistributionLp

/-!
# The finite signed maximal–square estimate

The density distribution bound and the convergent layer-cake argument
give a constant uniform for `1 ≤ p ≤ 3/2`. The reconstruction hypothesis in
the final theorem is explicit; no estimate for arbitrary input is claimed.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- First, estimate the sum of full interior differences using the
square of the original input. -/
theorem finite_difference_sum_square_integral
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (p : ℝ) (hp : 1 ≤ p) (hp3 : p ≤ (3 : ℝ) / 2) :
    (∫ x in productBox I,
      Real.rpow (finiteSignedProductMaximal I N
        (∑ Q ∈ productInterior I N, productDifferenceMap Finset.univ Q F) x) p) ≤
      (2 : ℝ) ^ (6 * (∑ i, d i) + 10) *
        ∫ x in productBox I, Real.rpow (finiteSquareFunction I N Finset.univ F x) p := by
  let G := ∑ Q ∈ productInterior I N, productDifferenceMap Finset.univ Q F
  have hG := productDifference_sum_productStep_closure I N F hf hs
    (productInterior I N) (fun _ h => h)
  have h := integral_rpow_le_of_dyadic_distribution I N
    (finiteSignedProductMaximal I N G) (finiteSquareFunction I N Finset.univ F)
    (productLeafConstant_finiteSignedProductMaximal I N G hG.1 hG.2)
    (productLeafConstant_finiteSquareFunction I N Finset.univ F hf hs)
    (fun x _ => finiteSignedProductMaximal_nonneg I N G x)
    (fun _ _ => Real.sqrt_nonneg _)
    ((2 : ℝ) ^ (6 * (∑ i, d i) + 5)) (by positivity)
    (finite_square_distribution I N hd F hf hs) p hp hp3
  have hc : 32 * (2 : ℝ) ^ (6 * (∑ i, d i) + 5) =
      (2 : ℝ) ^ (6 * (∑ i, d i) + 10) := by
    rw [show 6 * (∑ i, d i) + 10 = (6 * (∑ i, d i) + 5) + 5 by omega, pow_add]
    norm_num
    ring
  rw [hc] at h
  exact h

/-- The finite source estimate for an input equal to its full interior
martingale-difference sum, including `p = 1` and `p = 3/2`. -/
theorem finite_signed_square_integral
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (hreconstruct : F = ∑ Q ∈ productInterior I N, productDifferenceMap Finset.univ Q F)
    (p : ℝ) (hp : 1 ≤ p) (hp3 : p ≤ (3 : ℝ) / 2) :
    (∫ x in productBox I, Real.rpow (finiteSignedProductMaximal I N F x) p) ≤
      (2 : ℝ) ^ (6 * (∑ i, d i) + 10) *
        ∫ x in productBox I, Real.rpow (finiteSquareFunction I N Finset.univ F x) p := by
  have h := finite_difference_sum_square_integral I N hd F hf hs p hp hp3
  rw [← hreconstruct] at h
  exact h

/-- Taking power-integral norm roots retains a constant independent of
`p` throughout the closed interval `1 ≤ p ≤ 3/2`. -/
theorem finite_signed_square_lp
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (hreconstruct : F = ∑ Q ∈ productInterior I N, productDifferenceMap Finset.univ Q F)
    (p : ℝ) (hp : 1 ≤ p) (hp3 : p ≤ (3 : ℝ) / 2) :
    Real.rpow (∫ x in productBox I, Real.rpow (finiteSignedProductMaximal I N F x) p) (1 / p) ≤
      (2 : ℝ) ^ (6 * (∑ i, d i) + 10) *
        Real.rpow (∫ x in productBox I,
          Real.rpow (finiteSquareFunction I N Finset.univ F x) p) (1 / p) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hM0 : 0 ≤ ∫ x in productBox I,
      Real.rpow (finiteSignedProductMaximal I N F x) p :=
    integral_nonneg (fun x => Real.rpow_nonneg (finiteSignedProductMaximal_nonneg I N F x) p)
  have hS0 : 0 ≤ ∫ x in productBox I,
      Real.rpow (finiteSquareFunction I N Finset.univ F x) p :=
    integral_nonneg (fun _ => Real.rpow_nonneg (Real.sqrt_nonneg _) p)
  have hc1 : 1 ≤ (2 : ℝ) ^ (6 * (∑ i, d i) + 10) := one_le_pow₀ (by norm_num)
  have hc : Real.rpow ((2 : ℝ) ^ (6 * (∑ i, d i) + 10)) (1 / p) ≤
      (2 : ℝ) ^ (6 * (∑ i, d i) + 10) :=
    Real.rpow_le_self_of_one_le hc1 ((div_le_one hp0).mpr hp)
  calc
    _ ≤ Real.rpow ((2 : ℝ) ^ (6 * (∑ i, d i) + 10) *
        (∫ x in productBox I, Real.rpow (finiteSquareFunction I N Finset.univ F x) p)) (1 / p) :=
      Real.rpow_le_rpow hM0 (finite_signed_square_integral I N hd F hf hs hreconstruct p hp hp3)
        (by positivity)
    _ = Real.rpow ((2 : ℝ) ^ (6 * (∑ i, d i) + 10)) (1 / p) *
        Real.rpow (∫ x in productBox I,
          Real.rpow (finiteSquareFunction I N Finset.univ F x) p) (1 / p) := by
      simp only [Real.rpow_eq_pow]
      exact Real.mul_rpow (by positivity) hS0
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hS0 _)

end ReyZygmund
