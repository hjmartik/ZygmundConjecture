import ReyZygmund.Weighted.ProjectedHolder

/-!
# The projected-square and Hölder coefficients

The final step of the projected-square estimate replaces `(p - 1)⁻¹`
by `p / (p - 1)`. The Hölder estimate below uses that widened square bound
before taking norm roots.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- The projected square estimate, including its final comparison with `p'`.
The dimension coefficient is `m * 2 ^ (totalDim + m - 1)` and the averaging
family remains the denominator. -/
theorem projected_weighted_square_conjugate
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productRectangle I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
    let F := finiteInput I N f hf
    (∫ x in productRectangle I,
      (finiteComplementSquareFunction I N (finiteProjectionMap I N G F) x) ^ 2 /
        Real.rpow (finiteFamilyMaximal (averagingRectangles I N G) F x) (2 - p)) ≤
      ((m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)) *
        (p / (p - 1)) ^ (m - 1)) *
        ∫ x in productRectangle I, Real.rpow (f x) p := by
  have hs : 0 < p - 1 := sub_pos.mpr hp
  have hbase : 1 / (p - 1) ≤ p / (p - 1) :=
    div_le_div_of_nonneg_right hp.le hs.le
  have hcoefficient :
      (m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)) / (p - 1) ^ (m - 1) ≤
        (m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)) *
          (p / (p - 1)) ^ (m - 1) := by
    calc
      _ = ((m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1))) *
          (1 / (p - 1)) ^ (m - 1) := by
        simp only [div_eq_mul_inv, one_mul, inv_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (one_div_nonneg.mpr hs.le) hbase (m - 1))
        (mul_nonneg (Nat.cast_nonneg m) (pow_nonneg (by norm_num) _))
  exact (projected_weighted_square I N hd G hG f hf hfpos p hp hp2).trans
    (mul_le_mul_of_nonneg_right hcoefficient
      (integral_nonneg_of_ae (ae_restrict_of_forall_mem (measurableSet_productRectangle I)
        (fun x hx => Real.rpow_nonneg (hfpos x hx).le p))))

/-- Hölder with the projected-square coefficient, before taking the `p`th root. -/
theorem projected_holder_integral_conjugate
    (hm : 0 < m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productRectangle I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
    let F := finiteInput I N f hf
    let W := finiteComplementSquareFunction I N (finiteProjectionMap I N G F)
    let M := finiteFamilyMaximal (averagingRectangles I N G) F
    let K := (m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)) *
      (p / (p - 1)) ^ (m - 1)
    (∫ x in productRectangle I, Real.rpow (W x) p) ≤
      Real.rpow (K * ∫ x in productRectangle I, Real.rpow (f x) p) (p / 2) *
        Real.rpow (∫ x in productRectangle I, Real.rpow (M x) p) (1 - p / 2) := by
  let F := finiteInput I N f hf
  let P := finiteProjectionMap I N G F
  let W := finiteComplementSquareFunction I N P
  let M := finiteFamilyMaximal (averagingRectangles I N G) F
  let K := (m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)) *
    (p / (p - 1)) ^ (m - 1)
  change (∫ x in productRectangle I, Real.rpow (W x) p) ≤
    Real.rpow (K * ∫ x in productRectangle I, Real.rpow (f x) p) (p / 2) *
      Real.rpow (∫ x in productRectangle I, Real.rpow (M x) p) (1 - p / 2)
  have hF : ProductLeafConstant I N F.1 := productLeafConstant_indicator hf
  have hFs : ∀ x, x ∉ productRectangle I → F.1 x = 0 :=
    fun x hx => Set.indicator_of_notMem hx f
  have hFpos : ∀ x ∈ productRectangle I, 0 < F.1 x := by
    intro x hx
    change 0 < (productRectangle I).indicator f x
    rw [Set.indicator_of_mem hx]
    exact hfpos x hx
  have hP := finiteProjectionMap_productStep_closure I N G F hF hFs
  have hW : ProductLeafConstant I N W :=
    productLeafConstant_finiteComplementSquareFunction I N P hP.1 hP.2
  have hM : ProductLeafConstant I N M :=
    productLeafConstant_finiteFamilyMaximal I N (averagingRectangles I N G)
      (averagingRectangles_subset_productDescendants I N G) F
  have hW0 : ∀ x ∈ productRectangle I, 0 ≤ W x := fun x _ => Real.sqrt_nonneg _
  have hMpos : ∀ x ∈ productRectangle I, 0 < M x :=
    averagingFamilyMaximal_pos hm I N G hG F hFpos
  have hE0 : 0 ≤ ∫ x in productRectangle I, (W x) ^ 2 / Real.rpow (M x) (2 - p) :=
    integral_nonneg (fun x => div_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (finiteFamilyMaximal_nonneg _ F x) _))
  have hMp0 : 0 ≤ ∫ x in productRectangle I, Real.rpow (M x) p :=
    integral_nonneg (fun x => Real.rpow_nonneg (finiteFamilyMaximal_nonneg _ F x) p)
  calc
    _ ≤ Real.rpow (∫ x in productRectangle I, (W x) ^ 2 / Real.rpow (M x) (2 - p))
        (p / 2) * Real.rpow (∫ x in productRectangle I, Real.rpow (M x) p) (1 - p / 2) :=
      Weighted.weighted_energy_holder I N W M hW hM hW0 hMpos p hp hp2
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hE0
        (projected_weighted_square_conjugate I N hd G hG f hf hfpos p hp hp2)
        (by linarith)) (Real.rpow_nonneg hMp0 _)

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

private theorem sqrt_mul_pow (A q : ℝ) (hA : 0 ≤ A) (hq : 0 ≤ q) (k : ℕ) :
    Real.sqrt (A * q ^ k) = Real.sqrt A * Real.rpow q ((k : ℝ) / 2) := by
  have hhalf : (k : ℝ) * (1 / 2 : ℝ) = (k : ℝ) / 2 := by ring
  simp only [Real.sqrt_eq_rpow, Real.rpow_eq_pow]
  rw [Real.mul_rpow hA (pow_nonneg hq k), ← Real.rpow_natCast_mul hq, hhalf]

private theorem norm_half_power {a p : ℝ} (ha : 0 ≤ a) (hp : 0 < p) :
    Real.rpow (Real.rpow a (1 / p)) (p / 2) = Real.rpow a (1 / 2 : ℝ) := by
  have hexp : (1 / p) * (p / 2) = (1 / 2 : ℝ) := by
    rw [mul_comm]
    exact div_mul_div_cancel₀' hp.ne' 2 1
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul ha, hexp]

private theorem norm_complement_power {a : ℝ} (ha : 0 ≤ a) (p : ℝ) :
    Real.rpow (Real.rpow a (1 / p)) (1 - p / 2) =
      Real.rpow a ((2 - p) / (2 * p)) := by
  have hexp : (1 / p) * (1 - p / 2) = (2 - p) / (2 * p) := by
    rw [mul_comm, show 1 - p / 2 = (2 - p) / 2 by ring,
      div_mul_div_comm, mul_one]
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul ha, hexp]

/-- Hölder's inequality in norm variables. This proof uses the
projected-square bound before Hölder's norm roots, giving the real
half power `(p') ^ ((m - 1) / 2)`. The endpoint `p = 2` is retained. -/
theorem projected_holder_norm_variables_conjugate
    (hm : 0 < m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productRectangle I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
    let F := finiteInput I N f hf
    let W := finiteComplementSquareFunction I N (finiteProjectionMap I N G F)
    let M := finiteFamilyMaximal (averagingRectangles I N G) F
    let X := Real.rpow (∫ x in productRectangle I, Real.rpow (M x) p) (1 / p)
    let Y := Real.rpow (∫ x in productRectangle I, Real.rpow (f x) p) (1 / p)
    Real.rpow (∫ x in productRectangle I, Real.rpow (W x) p) (1 / p) ≤
      Real.sqrt ((m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1))) *
        Real.rpow (p / (p - 1)) (((m - 1 : ℕ) : ℝ) / 2) *
        Real.rpow Y (p / 2) * Real.rpow X (1 - p / 2) := by
  let F := finiteInput I N f hf
  let W := finiteComplementSquareFunction I N (finiteProjectionMap I N G F)
  let M := finiteFamilyMaximal (averagingRectangles I N G) F
  let U := ∫ x in productRectangle I, Real.rpow (f x) p
  let V := ∫ x in productRectangle I, Real.rpow (M x) p
  let A := (m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1))
  let q := p / (p - 1)
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hq : 0 ≤ q := div_nonneg hp0.le (sub_pos.mpr hp).le
  have hW0 : 0 ≤ ∫ x in productRectangle I, Real.rpow (W x) p :=
    integral_nonneg (fun _ => Real.rpow_nonneg (Real.sqrt_nonneg _) p)
  have hU : 0 ≤ U :=
    integral_nonneg_of_ae (ae_restrict_of_forall_mem (measurableSet_productRectangle I)
      (fun x hx => Real.rpow_nonneg (hfpos x hx).le p))
  have hV : 0 ≤ V :=
    integral_nonneg (fun x => Real.rpow_nonneg (finiteFamilyMaximal_nonneg _ F x) p)
  have hA : 0 ≤ A :=
    mul_nonneg (Nat.cast_nonneg m) (pow_nonneg (by norm_num) _)
  have h := holder_root_bound hW0 hU hV
    (mul_nonneg hA (pow_nonneg hq (m - 1))) hp0
    (projected_holder_integral_conjugate hm I N hd G hG f hf hfpos p hp hp2)
  change Real.rpow (∫ x in productRectangle I, Real.rpow (W x) p) (1 / p) ≤
    Real.sqrt (A * q ^ (m - 1)) * Real.rpow U (1 / 2 : ℝ) *
      Real.rpow V ((2 - p) / (2 * p)) at h
  rw [sqrt_mul_pow A q hA hq (m - 1),
    ← norm_half_power hU hp0, ← norm_complement_power hV p] at h
  exact h

end ReyZygmund
