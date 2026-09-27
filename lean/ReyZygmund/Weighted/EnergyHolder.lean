import ReyZygmund.Geometry.ProductIntegrability
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # The finite weighted Hölder estimate

Constancy on the smallest cubes gives integrability on the top rectangle,
including for the quotient energy. Values outside it are unrestricted. At `p = 2`
the estimate is an identity.

-/

open BoxIntegral MeasureTheory
open scoped ENNReal

namespace ReyZygmund.Weighted

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem memLp_of_productLeafConstant
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (r : ℝ) (hr : 0 < r)
    (hf : ProductLeafConstant I N f) :
    MemLp f (ENNReal.ofReal r) (volume.restrict (productBox I)) := by
  apply (integrable_norm_rpow_iff
    (integrableOn_productLeafConstant I N f hf).aestronglyMeasurable
    (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top).mp
  apply integrableOn_productLeafConstant I N
  intro Q hQ x hx y hy
  dsimp only
  rw [hf Q hQ x hx y hy]

private theorem weighted_power_factorization (u v p : ℝ) (hu : 0 ≤ u) (hv : 0 < v) :
    Real.rpow (u ^ 2 / Real.rpow v (2 - p)) (p / 2) *
        Real.rpow (Real.rpow v p) (1 - p / 2) = Real.rpow u p := by
  have huPower : (u ^ 2 : ℝ) ^ (p / 2) = u ^ p := by
    rw [← Real.rpow_two u, ← Real.rpow_mul hu,
      show (2 : ℝ) * (p / 2) = p by ring]
  have hvPower : (v ^ (2 - p)) ^ (p / 2) = (v ^ p) ^ (1 - p / 2) := by
    rw [← Real.rpow_mul hv.le, ← Real.rpow_mul hv.le]
    congr 1
    ring
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow (sq_nonneg u) (Real.rpow_nonneg hv.le (2 - p)) (p / 2),
    huPower, hvPower]
  exact div_mul_cancel₀ _
    (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hv p) (1 - p / 2)).ne'

private theorem integral_mul_rpow_le
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A B : ProductPoint d → ℝ)
    (hA : ProductLeafConstant I N A) (hB : ProductLeafConstant I N B)
    (hA0 : ∀ x ∈ productBox I, 0 ≤ A x) (hB0 : ∀ x ∈ productBox I, 0 ≤ B x)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∫ x in productBox I, Real.rpow (A x) θ * Real.rpow (B x) (1 - θ)) ≤
      Real.rpow (∫ x in productBox I, A x) θ *
        Real.rpow (∫ x in productBox I, B x) (1 - θ) := by
  let f : ProductPoint d → ℝ := fun x => Real.rpow (A x) θ
  let g : ProductPoint d → ℝ := fun x => Real.rpow (B x) (1 - θ)
  have hθc : 0 < 1 - θ := sub_pos.mpr hθ1
  have hpq := Real.HolderConjugate.inv_one_sub_inv hθ0 hθ1
  have hf : ProductLeafConstant I N f := by
    intro Q hQ x hx y hy
    exact congrArg (fun a => Real.rpow a θ) (hA Q hQ x hx y hy)
  have hg : ProductLeafConstant I N g := by
    intro Q hQ x hx y hy
    exact congrArg (fun b => Real.rpow b (1 - θ)) (hB Q hQ x hx y hy)
  have hf0 : 0 ≤ᵐ[volume.restrict (productBox I)] f := by
    filter_upwards [ae_restrict_mem (measurableSet_productBox I)] with x hx
    exact Real.rpow_nonneg (hA0 x hx) θ
  have hg0 : 0 ≤ᵐ[volume.restrict (productBox I)] g := by
    filter_upwards [ae_restrict_mem (measurableSet_productBox I)] with x hx
    exact Real.rpow_nonneg (hB0 x hx) (1 - θ)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hf0 hg0
    (memLp_of_productLeafConstant I N f θ⁻¹ hpq.pos hf)
    (memLp_of_productLeafConstant I N g (1 - θ)⁻¹ hpq.symm.pos hg)
  have hfPower : ∀ x ∈ productBox I, f x ^ θ⁻¹ = A x := by
    intro x hx
    dsimp only [f]
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul (hA0 x hx), mul_inv_cancel₀ hθ0.ne', Real.rpow_one]
  have hgPower : ∀ x ∈ productBox I, g x ^ (1 - θ)⁻¹ = B x := by
    intro x hx
    dsimp only [g]
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul (hB0 x hx), mul_inv_cancel₀ hθc.ne', Real.rpow_one]
  rw [setIntegral_congr_fun (measurableSet_productBox I) hfPower,
    setIntegral_congr_fun (measurableSet_productBox I) hgPower] at h
  simpa only [one_div, inv_inv, f, g, Real.rpow_eq_pow] using h

/-- The coefficient-one weighted Hölder estimate used before absorption.
The real exponent endpoint `p = 2` is included without a limiting argument. -/
theorem weighted_energy_holder
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (U V : ProductPoint d → ℝ)
    (hU : ProductLeafConstant I N U) (hV : ProductLeafConstant I N V)
    (hU0 : ∀ x ∈ productBox I, 0 ≤ U x) (hV0 : ∀ x ∈ productBox I, 0 < V x)
    (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
    (∫ x in productBox I, Real.rpow (U x) p) ≤
      Real.rpow (∫ x in productBox I, (U x) ^ 2 / Real.rpow (V x) (2 - p)) (p / 2) *
        Real.rpow (∫ x in productBox I, Real.rpow (V x) p) (1 - p / 2) := by
  rcases eq_or_lt_of_le hp2 with hpTwo | hpTwo
  · subst p
    norm_num [Real.rpow_eq_pow, Real.rpow_two]
  · let A : ProductPoint d → ℝ := fun x => (U x) ^ 2 / Real.rpow (V x) (2 - p)
    let B : ProductPoint d → ℝ := fun x => Real.rpow (V x) p
    have hA : ProductLeafConstant I N A := by
      intro Q hQ x hx y hy
      change (U x) ^ 2 / Real.rpow (V x) (2 - p) =
        (U y) ^ 2 / Real.rpow (V y) (2 - p)
      rw [hU Q hQ x hx y hy, hV Q hQ x hx y hy]
    have hB : ProductLeafConstant I N B := by
      intro Q hQ x hx y hy
      exact congrArg (fun v => Real.rpow v p) (hV Q hQ x hx y hy)
    have hA0 (x : ProductPoint d) (hx : x ∈ productBox I) : 0 ≤ A x :=
      div_nonneg (sq_nonneg _) (Real.rpow_nonneg (hV0 x hx).le (2 - p))
    have hB0 (x : ProductPoint d) (hx : x ∈ productBox I) : 0 ≤ B x :=
      Real.rpow_nonneg (hV0 x hx).le p
    have hfactor : ∀ x ∈ productBox I,
        Real.rpow (U x) p = Real.rpow (A x) (p / 2) * Real.rpow (B x) (1 - p / 2) := by
      intro x hx
      exact (weighted_power_factorization (U x) (V x) p (hU0 x hx) (hV0 x hx)).symm
    rw [setIntegral_congr_fun (measurableSet_productBox I) hfactor]
    exact integral_mul_rpow_le I N A B hA hB hA0 hB0 (p / 2) (by linarith) (by linarith)

end ReyZygmund.Weighted
