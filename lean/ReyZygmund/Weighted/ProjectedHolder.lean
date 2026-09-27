import ReyZygmund.Weighted.Projected
import ReyZygmund.Weighted.EnergyHolder

/-! # Hölder's inequality for the projected square function

The projection is constant on the smallest cubes, and the averaging-family maximal
function is positive on the top rectangle. These facts give the Hölder estimate
with coefficient one. Combining it with the weighted square estimate preserves the
explicit dimension and `p - 1` factors used in absorption.


-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

namespace Geometry

/-- The complement square function preserves constancy on the smallest cubes,
including in zero-dimensional factors. -/
theorem productLeafConstant_finiteComplementSquareFunction
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) :
    ProductLeafConstant I N (finiteComplementSquareFunction I N F) := by
  intro P hP x hx y hy
  simp only [finiteComplementSquareFunction_eq_partial]
  apply congrArg Real.sqrt
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z : ℝ => z ^ 2)
    (productLeafConstant_finiteSquareFunction I N (Finset.univ.erase j)
      F hf hs P hP x hx y hy)

end Geometry

/-- The Hölder estimate in p-th-power integral form uses the projection, averaging
family and weighted square constant. Incomparability and hypotheses outside the
top rectangle are not required. -/
theorem projected_holder_integral
    (hm : 0 < m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productBox I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
    let F := finiteInput I N f hf
    let W := finiteComplementSquareFunction I N (finiteProjectionMap I N G F)
    let M := finiteFamilyMaximal (averagingRectangles I N G) F
    let K := (m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)) / (p - 1) ^ (m - 1)
    (∫ x in productBox I, Real.rpow (W x) p) ≤
      Real.rpow (K * ∫ x in productBox I, Real.rpow (f x) p) (p / 2) *
        Real.rpow (∫ x in productBox I, Real.rpow (M x) p) (1 - p / 2) := by
  let F := finiteInput I N f hf
  let P := finiteProjectionMap I N G F
  let W := finiteComplementSquareFunction I N P
  let M := finiteFamilyMaximal (averagingRectangles I N G) F
  let K := (m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)) / (p - 1) ^ (m - 1)
  change (∫ x in productBox I, Real.rpow (W x) p) ≤
    Real.rpow (K * ∫ x in productBox I, Real.rpow (f x) p) (p / 2) *
      Real.rpow (∫ x in productBox I, Real.rpow (M x) p) (1 - p / 2)
  have hF : ProductLeafConstant I N F.1 := productLeafConstant_indicator hf
  have hFs : ∀ x, x ∉ productBox I → F.1 x = 0 :=
    fun x hx => Set.indicator_of_notMem hx f
  have hFpos : ∀ x ∈ productBox I, 0 < F.1 x := by
    intro x hx
    change 0 < (productBox I).indicator f x
    rw [Set.indicator_of_mem hx]
    exact hfpos x hx
  have hP := finiteProjectionMap_productStep_closure I N G F hF hFs
  have hW : ProductLeafConstant I N W :=
    productLeafConstant_finiteComplementSquareFunction I N P hP.1 hP.2
  have hM : ProductLeafConstant I N M :=
    productLeafConstant_finiteFamilyMaximal I N (averagingRectangles I N G)
      (averagingRectangles_subset_productDescendants I N G) F
  have hW0 : ∀ x ∈ productBox I, 0 ≤ W x :=
    fun x _ => Real.sqrt_nonneg _
  have hMpos : ∀ x ∈ productBox I, 0 < M x :=
    averagingFamilyMaximal_pos hm I N G hG F hFpos
  have hE0 : 0 ≤ ∫ x in productBox I, (W x) ^ 2 / Real.rpow (M x) (2 - p) :=
    integral_nonneg (fun x => div_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (finiteFamilyMaximal_nonneg _ F x) _))
  have hMp0 : 0 ≤ ∫ x in productBox I, Real.rpow (M x) p :=
    integral_nonneg (fun x => Real.rpow_nonneg (finiteFamilyMaximal_nonneg _ F x) p)
  calc
    _ ≤ Real.rpow (∫ x in productBox I, (W x) ^ 2 / Real.rpow (M x) (2 - p))
        (p / 2) * Real.rpow (∫ x in productBox I, Real.rpow (M x) p) (1 - p / 2) :=
      Weighted.weighted_energy_holder I N W M hW hM hW0 hMpos p hp hp2
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hE0
        (projected_weighted_square I N hd G hG f hf hfpos p hp hp2) (by linarith))
      (Real.rpow_nonneg hMp0 _)

private theorem holder_root_bound {A B C K p : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hK : 0 ≤ K) (hp : 0 < p)
    (h : A ≤ Real.rpow (K * B) (p / 2) * Real.rpow C (1 - p / 2)) :
    Real.rpow A (1 / p) ≤
      Real.sqrt K * Real.rpow B (1 / 2 : ℝ) * Real.rpow C ((2 - p) / (2 * p)) := by
  have hhalf : (p / 2) * (1 / p) = (1 / 2 : ℝ) :=
    div_mul_div_cancel₀' hp.ne' 2 1
  have hother : (1 - p / 2) * (1 / p) = (2 - p) / (2 * p) := by
    rw [show 1 - p / 2 = (2 - p) / 2 by ring, div_mul_div_comm, mul_one]
  calc
    _ ≤ Real.rpow (Real.rpow (K * B) (p / 2) * Real.rpow C (1 - p / 2)) (1 / p) :=
      Real.rpow_le_rpow hA h (one_div_nonneg.mpr hp.le)
    _ = _ := by
      simp only [Real.rpow_eq_pow]
      rw [Real.mul_rpow (Real.rpow_nonneg (mul_nonneg hK hB) _)
        (Real.rpow_nonneg hC _), ← Real.rpow_mul (mul_nonneg hK hB),
        ← Real.rpow_mul hC, hhalf, hother, Real.mul_rpow hK hB, Real.sqrt_eq_rpow]

/-- The Hölder estimate in norm form before absorption, with `sqrt K` and the stated
exponent of the averaging-family maximal integral. -/
theorem projected_holder_norm
    (hm : 0 < m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productBox I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
    let F := finiteInput I N f hf
    let W := finiteComplementSquareFunction I N (finiteProjectionMap I N G F)
    let M := finiteFamilyMaximal (averagingRectangles I N G) F
    let K := (m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)) / (p - 1) ^ (m - 1)
    Real.rpow (∫ x in productBox I, Real.rpow (W x) p) (1 / p) ≤
      Real.sqrt K * Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / 2 : ℝ) *
        Real.rpow (∫ x in productBox I, Real.rpow (M x) p) ((2 - p) / (2 * p)) := by
  let F := finiteInput I N f hf
  let W := finiteComplementSquareFunction I N (finiteProjectionMap I N G F)
  let M := finiteFamilyMaximal (averagingRectangles I N G) F
  let K := (m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)) / (p - 1) ^ (m - 1)
  change Real.rpow (∫ x in productBox I, Real.rpow (W x) p) (1 / p) ≤
    Real.sqrt K * Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / 2 : ℝ) *
      Real.rpow (∫ x in productBox I, Real.rpow (M x) p) ((2 - p) / (2 * p))
  have hWp0 : 0 ≤ ∫ x in productBox I, Real.rpow (W x) p :=
    integral_nonneg (fun _ => Real.rpow_nonneg (Real.sqrt_nonneg _) p)
  have hfp0 : 0 ≤ ∫ x in productBox I, Real.rpow (f x) p :=
    integral_nonneg_of_ae (ae_restrict_of_forall_mem (measurableSet_productBox I)
      (fun x hx => Real.rpow_nonneg (hfpos x hx).le p))
  have hMp0 : 0 ≤ ∫ x in productBox I, Real.rpow (M x) p :=
    integral_nonneg (fun x => Real.rpow_nonneg (finiteFamilyMaximal_nonneg _ F x) p)
  have hK0 : 0 ≤ K :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg m) (pow_nonneg (by norm_num) _))
      (pow_nonneg (sub_nonneg.mpr hp.le) _)
  exact holder_root_bound hWp0 hfp0 hMp0 hK0 (lt_trans zero_lt_one hp)
    (projected_holder_integral hm I N hd G hG f hf hfpos p hp hp2)

end ReyZygmund
