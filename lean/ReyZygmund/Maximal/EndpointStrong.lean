import ReyZygmund.Maximal.EndpointTonelli
import ReyZygmund.Maximal.EndpointKernel

/-! # Quantitative strong bounds from the truncated endpoint distribution

The exact scalar kernel is inserted into the layer-cake/Tonelli
identity. The only simplification of the p-dependent coefficient is
2^p * p ≤ 8 for 1 < p ≤ 2.
-/

open MeasureTheory Set
open scoped ENNReal

namespace ReyZygmund

private theorem input_kernel_factor (u p : ℝ) (hu : 0 ≤ u) (hp : 1 < p) :
    u * (2 * u) ^ (p - 1) = (2 : ℝ) ^ (p - 1) * u ^ p := by
  rw [Real.mul_rpow (by norm_num) hu]
  have hpower : u ^ (p - 1) * u = u ^ p := by
    have h := Real.rpow_add_of_nonneg hu
      (show 0 ≤ p - 1 by linarith) (show (0 : ℝ) ≤ 1 by norm_num)
    simpa only [sub_add_cancel, Real.rpow_one] using h.symm
  calc
    u * ((2 : ℝ) ^ (p - 1) * u ^ (p - 1)) =
        (2 : ℝ) ^ (p - 1) * (u ^ (p - 1) * u) := by ring
    _ = _ := by rw [hpower]

/-- The strong power estimate with the paper's explicit p dependence.
All nonnegative integrals retain their values, including infinity. -/
theorem endpoint_distribution_strong_power
    {X : Type} [MeasurableSpace X] (mu : Measure X) [SFinite mu]
    (f F : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (k : ℕ) (p A : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) (hA : 0 ≤ A)
    (hlevel : ∀ t : ℝ, 0 < t →
      mu {x | t < F x} ≤ ENNReal.ofReal (2 * A / t) *
        ∫⁻ x in {x | t / 2 < f x}, ENNReal.ofReal
          (f x * (Real.log (Real.exp 1 + 2 * f x / t)) ^ k) ∂mu) :
    (∫⁻ x, ENNReal.ofReal (F x ^ p) ∂mu) ≤
      ENNReal.ofReal (8 * A * Real.exp 2 * (k.factorial : ℝ) /
        (p - 1) ^ (k + 1)) *
          ∫⁻ x, ENNReal.ofReal (f x ^ p) ∂mu := by
  let K : ℝ := Real.exp 2 * (k.factorial : ℝ) / (p - 1) ^ (k + 1)
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hpoint (x : X) :
      ENNReal.ofReal (f x) *
        (∫⁻ t in Ioo (0 : ℝ) (2 * f x), ENNReal.ofReal
          (t ^ (p - 2) * (Real.log (Real.exp 1 + 2 * f x / t)) ^ k)) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (p - 1) * K) * ENNReal.ofReal (f x ^ p) := by
    have hkernel := endpoint_truncated_log_kernel k p (f x) hp hp2 (hf0 x)
    simp only [Real.rpow_eq_pow] at hkernel
    calc
      _ ≤ ENNReal.ofReal (f x) *
          ENNReal.ofReal ((2 * f x) ^ (p - 1) * Real.exp 2 *
            (k.factorial : ℝ) / (p - 1) ^ (k + 1)) :=
        mul_le_mul_right hkernel _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (hf0 x),
          ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hK)]
        congr 1
        dsimp only [K]
        calc
          _ = (f x * (2 * f x) ^ (p - 1)) *
              (Real.exp 2 * (k.factorial : ℝ) / (p - 1) ^ (k + 1)) := by ring
          _ = _ := by rw [input_kernel_factor (f x) p (hf0 x) hp]; ring
  have htwo : (2 : ℝ) ^ (p - 1) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show p - 1 ≤ 1 by linarith)
    simpa only [Real.rpow_one] using h
  have hcoeff : (2 * A * p) * ((2 : ℝ) ^ (p - 1) * K) ≤
      8 * A * Real.exp 2 * (k.factorial : ℝ) / (p - 1) ^ (k + 1) := by
    calc
      _ ≤ (2 * A * 2) * (2 * K) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left hp2 (by positivity))
          (mul_le_mul_of_nonneg_right htwo hK)
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hK) (by positivity)
      _ = _ := by dsimp only [K]; ring
  calc
    _ ≤ ENNReal.ofReal (2 * A * p) * ∫⁻ x, ENNReal.ofReal (f x) *
        ∫⁻ t in Ioo (0 : ℝ) (2 * f x), ENNReal.ofReal
          (t ^ (p - 2) * (Real.log (Real.exp 1 + 2 * f x / t)) ^ k) ∂volume ∂mu :=
      lintegral_rpow_le_endpoint_kernel mu f F hf hf0 hF hF0 k p A hp0 hA hlevel
    _ ≤ ENNReal.ofReal (2 * A * p) *
        ∫⁻ x, ENNReal.ofReal ((2 : ℝ) ^ (p - 1) * K) *
          ENNReal.ofReal (f x ^ p) ∂mu :=
      mul_le_mul_right (lintegral_mono hpoint) _
    _ = ENNReal.ofReal ((2 * A * p) * ((2 : ℝ) ^ (p - 1) * K)) *
        ∫⁻ x, ENNReal.ofReal (f x ^ p) ∂mu := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * A * p)]
    _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal hcoeff) _

end ReyZygmund
