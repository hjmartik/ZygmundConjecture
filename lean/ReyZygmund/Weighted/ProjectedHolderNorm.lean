import ReyZygmund.Weighted.ProjectedHolder

/-! # The projected Hölder estimate in norm form

Rewrite the power-integral estimate using the norms of the input, the square
function of its projection, and the averaging-family maximal function. Separate
the dimension factor from the power of `p - 1`. No norm is divided out, so zero
norms are included. The subsequent absorption step is proved separately.


-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

private theorem sqrt_div_pow_factor (A s : ℝ) (hA : 0 ≤ A) (hs : 0 ≤ s) (k : ℕ) :
    Real.sqrt (A / s ^ k) =
      Real.sqrt A * Real.rpow s (-((k : ℕ) : ℝ) / 2) := by
  simp only [Real.sqrt_eq_rpow, Real.rpow_eq_pow]
  rw [Real.div_rpow hA (pow_nonneg hs k) (1 / 2),
    ← Real.rpow_natCast_mul hs k (1 / 2)]
  rw [show (k : ℝ) * (1 / 2 : ℝ) = (k : ℝ) / 2 by ring,
    show -(k : ℝ) / 2 = -((k : ℝ) / 2) by ring,
    Real.rpow_neg hs, div_eq_mul_inv]

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

variable {m : ℕ} {d : Fin m → ℕ}

/-- The projected Hölder bound with the norm variables and exact
coefficient used in the subsequent absorption step. Real powers retain zero
integrals and the endpoint `p = 2` without cancellation. -/
theorem projected_holder_norm_variables
    (hm : 0 < m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productBox I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
    let F := finiteInput I N f hf
    let W := finiteComplementSquareFunction I N (finiteProjectionMap I N G F)
    let M := finiteFamilyMaximal (averagingRectangles I N G) F
    let X := Real.rpow (∫ x in productBox I, Real.rpow (M x) p) (1 / p)
    let Y := Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p)
    Real.rpow (∫ x in productBox I, Real.rpow (W x) p) (1 / p) ≤
      Real.sqrt ((m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1))) *
        Real.rpow (p - 1) (-((m - 1 : ℕ) : ℝ) / 2) *
        Real.rpow Y (p / 2) * Real.rpow X (1 - p / 2) := by
  let F := finiteInput I N f hf
  let W := finiteComplementSquareFunction I N (finiteProjectionMap I N G F)
  let M := finiteFamilyMaximal (averagingRectangles I N G) F
  let U := ∫ x in productBox I, Real.rpow (f x) p
  let V := ∫ x in productBox I, Real.rpow (M x) p
  let A := (m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1))
  change Real.rpow (∫ x in productBox I, Real.rpow (W x) p) (1 / p) ≤
    Real.sqrt A * Real.rpow (p - 1) (-((m - 1 : ℕ) : ℝ) / 2) *
      Real.rpow (Real.rpow U (1 / p)) (p / 2) *
      Real.rpow (Real.rpow V (1 / p)) (1 - p / 2)
  have hU : 0 ≤ U :=
    integral_nonneg_of_ae (ae_restrict_of_forall_mem (measurableSet_productBox I)
      (fun x hx => Real.rpow_nonneg (hfpos x hx).le p))
  have hV : 0 ≤ V :=
    integral_nonneg (fun x => Real.rpow_nonneg (finiteFamilyMaximal_nonneg _ F x) p)
  have hA : 0 ≤ A :=
    mul_nonneg (Nat.cast_nonneg m) (pow_nonneg (by norm_num) _)
  have h := projected_holder_norm hm I N hd G hG f hf hfpos p hp hp2
  change Real.rpow (∫ x in productBox I, Real.rpow (W x) p) (1 / p) ≤
    Real.sqrt (A / (p - 1) ^ (m - 1)) * Real.rpow U (1 / 2 : ℝ) *
      Real.rpow V ((2 - p) / (2 * p)) at h
  rw [sqrt_div_pow_factor A (p - 1) hA (sub_nonneg.mpr hp.le) (m - 1),
    ← norm_half_power hU (lt_trans zero_lt_one hp), ← norm_complement_power hV p] at h
  exact h

end ReyZygmund
