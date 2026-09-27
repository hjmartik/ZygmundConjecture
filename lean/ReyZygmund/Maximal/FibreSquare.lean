import ReyZygmund.Geometry.CoordinateFibreOperators
import ReyZygmund.Geometry.FibreIntegration
import ReyZygmund.Maximal.Square
import Mathlib.Algebra.BigOperators.Fin

/-! # A partial maximal–square estimate by slicing

Apply the lower-dimensional estimate to each bounded measurable slice. Identities
for the operators and indices identify its signed maximum and square function.
Fubini then gives the partial difference-sum estimate on the top rectangle, used
in the maximal-to-square reduction.


-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {n : ℕ} {d : Fin (n + 1) → ℕ}

private theorem partial_difference_sum_closure
    (I : ∀ i, Box (Fin (d i))) (N : Fin (n + 1) → ℕ)
    (A : Finset (Fin (n + 1)))
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) :
    ProductLeafConstant I N
        (∑ Q ∈ partialInterior I N A, productDifferenceMap A Q F).1 ∧
      ∀ x, x ∉ productBox I →
        (∑ Q ∈ partialInterior I N A, productDifferenceMap A Q F).1 x = 0 := by
  have hc Q (hQ : Q ∈ partialInterior I N A) :=
    productDifferenceMap_productStep_closure I N F hf hs A Q
      (fun i hi => partialInterior_mem_selected hQ hi)
  constructor
  · simpa only [Submodule.coe_sum] using
      productLeafConstant_finsetSum (partialInterior I N A)
        (fun Q => (productDifferenceMap A Q F).1) (fun Q hQ => (hc Q hQ).1)
  · intro x hx
    simp only [Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_eq_zero (fun Q hQ => (hc Q hQ).2 x hx)

private theorem sum_fibre_dimensions_le (j : Fin (n + 1)) :
    (∑ i : Fin n, d (j.succAbove i)) ≤ ∑ i, d i := by
  rw [Fin.sum_univ_succAbove d j]
  omega

private theorem partial_difference_sum_fibre_integral
    (I : ∀ i, Box (Fin (d i))) (N : Fin (n + 1) → ℕ) (hd : ∀ i, 0 < d i)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (j : Fin (n + 1)) (t : Fin (d j) → ℝ) (ht : t ∈ I j)
    (p : ℝ) (hp : 1 ≤ p) (hp3 : p ≤ (3 : ℝ) / 2) :
    (∫ y in productBox (fun i => I (j.succAbove i)),
      Real.rpow (finiteSignedPartialMaximal I N (Finset.univ.erase j)
        (∑ Q ∈ partialInterior I N (Finset.univ.erase j),
          productDifferenceMap (Finset.univ.erase j) Q F) (j.insertNth t y)) p) ≤
      (2 : ℝ) ^ (6 * (∑ i, d i) + 10) *
        ∫ y in productBox (fun i => I (j.succAbove i)),
          Real.rpow (finiteSquareFunction I N (Finset.univ.erase j) F (j.insertNth t y)) p := by
  have hft : ProductLeafConstant (fun i => I (j.succAbove i))
      (fun i => N (j.succAbove i)) (coordinateFibreMap j t F).1 := by
    change ProductLeafConstant (fun i => I (j.succAbove i))
      (fun i => N (j.succAbove i)) (fun y => F.1 (j.insertNth t y))
    exact productLeafConstant_coordinateFibre I N F.1 hf j t ht
  have hst : ∀ y, y ∉ productBox (fun i => I (j.succAbove i)) →
      (coordinateFibreMap j t F).1 y = 0 := by
    intro y hy
    exact coordinateFibre_eq_zero_of_notMem_root I F.1 hs j t y hy
  have h := finite_difference_sum_square_integral
    (fun i => I (j.succAbove i)) (fun i => N (j.succAbove i))
    (fun i => hd (j.succAbove i)) (coordinateFibreMap j t F) hft hst p hp hp3
  have hc : (2 : ℝ) ^ (6 * (∑ i : Fin n, d (j.succAbove i)) + 10) ≤
      (2 : ℝ) ^ (6 * (∑ i, d i) + 10) := by
    apply pow_le_pow_right₀ (by norm_num)
    have hdim := sum_fibre_dimensions_le (d := d) j
    omega
  have hS : 0 ≤ ∫ y in productBox (fun i => I (j.succAbove i)),
      Real.rpow (finiteSquareFunction (fun i => I (j.succAbove i))
        (fun i => N (j.succAbove i)) Finset.univ (coordinateFibreMap j t F) y) p :=
    integral_nonneg (fun _ => Real.rpow_nonneg (Real.sqrt_nonneg _) p)
  have h' := h.trans (mul_le_mul_of_nonneg_right hc hS)
  simpa only [finiteSignedPartialMaximal_coordinateFibre,
    coordinateFibreMap_difference_sum, finiteSquareFunction_coordinateFibre] using h'

/-- The signed partial maximum of the partial difference sum is
controlled by the original input's partial square, with a p-independent
coefficient. All integrals are over the top rectangle. -/
theorem finite_partial_difference_sum_square_integral
    (I : ∀ i, Box (Fin (d i))) (N : Fin (n + 1) → ℕ) (hd : ∀ i, 0 < d i)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (j : Fin (n + 1)) (p : ℝ) (hp : 1 ≤ p) (hp3 : p ≤ (3 : ℝ) / 2) :
    (∫ x in productBox I,
      Real.rpow (finiteSignedPartialMaximal I N (Finset.univ.erase j)
        (∑ Q ∈ partialInterior I N (Finset.univ.erase j),
          productDifferenceMap (Finset.univ.erase j) Q F) x) p) ≤
      (2 : ℝ) ^ (6 * (∑ i, d i) + 10) *
        ∫ x in productBox I,
          Real.rpow (finiteSquareFunction I N (Finset.univ.erase j) F x) p := by
  let A := (Finset.univ : Finset (Fin (n + 1))).erase j
  let G := ∑ Q ∈ partialInterior I N A, productDifferenceMap A Q F
  have hG := partial_difference_sum_closure I N A F hf hs
  have hmax := productLeafConstant_finiteSignedPartialMaximal I N A G hG.1 hG.2
  have hsq := productLeafConstant_finiteSquareFunction I N A F hf hs
  have hM : ProductLeafConstant I N
      (fun x => Real.rpow (finiteSignedPartialMaximal I N A G x) p) := by
    intro Q hQ x hx y hy
    exact congrArg (fun a : ℝ => Real.rpow a p) (hmax Q hQ x hx y hy)
  have hS : ProductLeafConstant I N
      (fun x => Real.rpow (finiteSquareFunction I N A F x) p) := by
    intro Q hQ x hx y hy
    exact congrArg (fun a : ℝ => Real.rpow a p) (hsq Q hQ x hx y hy)
  change (∫ x in productBox I, Real.rpow (finiteSignedPartialMaximal I N A G x) p) ≤
    (2 : ℝ) ^ (6 * (∑ i, d i) + 10) *
      ∫ x in productBox I, Real.rpow (finiteSquareFunction I N A F x) p
  rw [integral_product_coordinateFibre I N _ hM j,
    integral_product_coordinateFibre I N _ hS j, ← integral_const_mul]
  apply setIntegral_mono_on
    (integrableOn_coordinateFibre_integral I N _ hM j)
    ((integrableOn_coordinateFibre_integral I N _ hS j).const_mul
      ((2 : ℝ) ^ (6 * (∑ i, d i) + 10))) (I j).measurableSet_coe
  intro t ht
  exact partial_difference_sum_fibre_integral I N hd F hf hs j t ht p hp hp3

/-- Taking the power-integral roots preserves the same uniform
coefficient, including both endpoints and an empty remaining product. -/
theorem finite_partial_difference_sum_square_lp
    (I : ∀ i, Box (Fin (d i))) (N : Fin (n + 1) → ℕ) (hd : ∀ i, 0 < d i)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (j : Fin (n + 1)) (p : ℝ) (hp : 1 ≤ p) (hp3 : p ≤ (3 : ℝ) / 2) :
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteSignedPartialMaximal I N (Finset.univ.erase j)
        (∑ Q ∈ partialInterior I N (Finset.univ.erase j),
          productDifferenceMap (Finset.univ.erase j) Q F) x) p) (1 / p) ≤
      (2 : ℝ) ^ (6 * (∑ i, d i) + 10) *
        Real.rpow (∫ x in productBox I,
          Real.rpow (finiteSquareFunction I N (Finset.univ.erase j) F x) p) (1 / p) := by
  let G := ∑ Q ∈ partialInterior I N (Finset.univ.erase j),
    productDifferenceMap (Finset.univ.erase j) Q F
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hM0 : 0 ≤ ∫ x in productBox I,
      Real.rpow (finiteSignedPartialMaximal I N (Finset.univ.erase j) G x) p :=
    integral_nonneg (fun x => Real.rpow_nonneg
      (finiteSignedPartialMaximal_nonneg I N (Finset.univ.erase j) G x) p)
  have hS0 : 0 ≤ ∫ x in productBox I,
      Real.rpow (finiteSquareFunction I N (Finset.univ.erase j) F x) p :=
    integral_nonneg (fun _ => Real.rpow_nonneg (Real.sqrt_nonneg _) p)
  have hc1 : 1 ≤ (2 : ℝ) ^ (6 * (∑ i, d i) + 10) := one_le_pow₀ (by norm_num)
  have hc : Real.rpow ((2 : ℝ) ^ (6 * (∑ i, d i) + 10)) (1 / p) ≤
      (2 : ℝ) ^ (6 * (∑ i, d i) + 10) :=
    Real.rpow_le_self_of_one_le hc1 ((div_le_one hp0).mpr hp)
  calc
    _ ≤ Real.rpow ((2 : ℝ) ^ (6 * (∑ i, d i) + 10) *
        (∫ x in productBox I,
          Real.rpow (finiteSquareFunction I N (Finset.univ.erase j) F x) p)) (1 / p) :=
      Real.rpow_le_rpow hM0
        (finite_partial_difference_sum_square_integral I N hd F hf hs j p hp hp3)
        (by positivity)
    _ = Real.rpow ((2 : ℝ) ^ (6 * (∑ i, d i) + 10)) (1 / p) *
        Real.rpow (∫ x in productBox I,
          Real.rpow (finiteSquareFunction I N (Finset.univ.erase j) F x) p) (1 / p) := by
      simp only [Real.rpow_eq_pow]
      exact Real.mul_rpow (by positivity) hS0
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hS0 _)

end ReyZygmund
