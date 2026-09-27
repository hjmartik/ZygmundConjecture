import ReyZygmund.Geometry.ProductIntegrability
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # Power-integral norms on the top rectangle

Constancy on the smallest cubes gives membership in every finite positive Lp space
on the top rectangle. The triangle, finite-sum, scalar and order inequalities then
apply to the power integrals used in the finite maximal estimate. No sign or
support restriction is imposed.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- Membership is derived from constancy on the smallest cubes, including for nonlinear
finite energies. It is not an extra hypothesis of the subsequent norm bounds. -/
theorem memLp_productLeafConstant
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (p : ℝ) (hp : 0 < p) :
    MemLp f (ENNReal.ofReal p) (volume.restrict (productBox I)) := by
  apply (integrable_norm_rpow_iff
    (integrableOn_productLeafConstant I N f hf).aestronglyMeasurable
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top).mp
  apply integrableOn_productLeafConstant I N
  intro Q hQ x hx y hy
  dsimp only
  rw [hf Q hQ x hx y hy]

/-- Mathlib's real Lp norm is exactly the power-integral expression. -/
theorem lpNorm_productLeafConstant_eq
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (p : ℝ) (hp : 0 < p) :
    lpNorm f (ENNReal.ofReal p) (volume.restrict (productBox I)) =
      Real.rpow (∫ x in productBox I, Real.rpow |f x| p) (1 / p) := by
  simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs, one_div,
    Real.rpow_eq_pow] using
    lpNorm_eq_integral_norm_rpow_toReal (ENNReal.ofReal_ne_zero_iff.mpr hp)
      ENNReal.ofReal_ne_top (integrableOn_productLeafConstant I N f hf).aestronglyMeasurable

/-- The norm triangle inequality on the top rectangle, with coefficient one. -/
theorem rootLp_add_le
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f g : ProductPoint d → ℝ)
    (hf : ProductLeafConstant I N f) (hg : ProductLeafConstant I N g)
    (p : ℝ) (hp : 1 ≤ p) :
    Real.rpow (∫ x in productBox I, Real.rpow |f x + g x| p) (1 / p) ≤
      Real.rpow (∫ x in productBox I, Real.rpow |f x| p) (1 / p) +
        Real.rpow (∫ x in productBox I, Real.rpow |g x| p) (1 / p) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hfg : ProductLeafConstant I N (f + g) := by
    intro Q hQ x hx y hy
    change f x + g x = f y + g y
    rw [hf Q hQ x hx y hy, hg Q hQ x hx y hy]
  have h := lpNorm_add_le (memLp_productLeafConstant I N f hf p hp0)
    (g := g) (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)
  simpa only [lpNorm_productLeafConstant_eq I N _ hfg p hp0,
    lpNorm_productLeafConstant_eq I N _ hf p hp0,
    lpNorm_productLeafConstant_eq I N _ hg p hp0, Pi.add_apply] using h

/-- Finite summation does not introduce an exponent-dependent constant. -/
theorem rootLp_sum_le {α : Type*}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (s : Finset α) (f : α → ProductPoint d → ℝ)
    (hf : ∀ a ∈ s, ProductLeafConstant I N (f a)) (p : ℝ) (hp : 1 ≤ p) :
    Real.rpow (∫ x in productBox I, Real.rpow |∑ a ∈ s, f a x| p) (1 / p) ≤
      ∑ a ∈ s, Real.rpow (∫ x in productBox I, Real.rpow |f a x| p) (1 / p) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hsum : ProductLeafConstant I N (∑ a ∈ s, f a) := by
    intro Q hQ x hx y hy
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun a ha => hf a ha Q hQ x hx y hy)
  have h := lpNorm_sum_le (fun a ha => memLp_productLeafConstant I N (f a) (hf a ha) p hp0)
    (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)
  rw [lpNorm_productLeafConstant_eq I N _ hsum p hp0] at h
  simp only [Finset.sum_apply] at h
  convert h using 1
  exact Finset.sum_congr rfl (fun a ha =>
    (lpNorm_productLeafConstant_eq I N _ (hf a ha) p hp0).symm)

/-- Multiplication costs precisely the absolute value of the scalar. -/
theorem rootLp_const_mul
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (c p : ℝ) (hp : 0 < p) :
    Real.rpow (∫ x in productBox I, Real.rpow |c * f x| p) (1 / p) =
      |c| * Real.rpow (∫ x in productBox I, Real.rpow |f x| p) (1 / p) := by
  have hcf : ProductLeafConstant I N (c • f) := by
    intro Q hQ x hx y hy
    change c * f x = c * f y
    rw [hf Q hQ x hx y hy]
  have h := lpNorm_const_smul c f (volume.restrict (productBox I)) (p := ENNReal.ofReal p)
  simpa only [lpNorm_productLeafConstant_eq I N _ hcf p hp,
    lpNorm_productLeafConstant_eq I N _ hf p hp, Pi.smul_apply, smul_eq_mul,
    coe_nnnorm, Real.norm_eq_abs] using h

/-- Pointwise comparison is required only on the top rectangle. -/
theorem rootLp_mono
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f g : ProductPoint d → ℝ)
    (hf : ProductLeafConstant I N f) (hg : ProductLeafConstant I N g)
    (hfg : ∀ x ∈ productBox I, |f x| ≤ |g x|)
    (p : ℝ) (hp : 0 < p) :
    Real.rpow (∫ x in productBox I, Real.rpow |f x| p) (1 / p) ≤
      Real.rpow (∫ x in productBox I, Real.rpow |g x| p) (1 / p) := by
  have hi (u : ProductPoint d → ℝ) (hu : ProductLeafConstant I N u) :
      IntegrableOn (fun x => Real.rpow |u x| p) (productBox I) volume := by
    apply integrableOn_productLeafConstant I N
    intro Q hQ x hx y hy
    exact congrArg (fun v => Real.rpow |v| p) (hu Q hQ x hx y hy)
  apply Real.rpow_le_rpow (integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _))
    _ (by positivity)
  apply setIntegral_mono_on (hi f hf) (hi g hg) (measurableSet_productBox I)
  intro x hx
  exact Real.rpow_le_rpow (abs_nonneg _) (hfg x hx) hp.le

end ReyZygmund.Geometry
