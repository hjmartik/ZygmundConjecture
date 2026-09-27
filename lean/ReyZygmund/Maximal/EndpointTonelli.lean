import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp

/-! # The nonnegative integration step in endpoint interpolation

All integrals here are extended nonnegative integrals. In particular the
order of integration can be changed before proving the resulting Lp bound.
The interval for the inner scalar kernel is exactly `(0,2*f x)`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace ReyZygmund

/-- The exact Tonelli identity after removing the input below half the level.
This is the middle line of formula (26) in the admitted support proof. -/
theorem endpoint_truncated_moment_swap
    {X : Type} [MeasurableSpace X] (mu : Measure X) [SFinite mu]
    (f : X → ℝ) (hm : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (k : ℕ) (p A : ℝ) (hA : 0 ≤ A) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 1)) *
      (ENNReal.ofReal (2 * A / t) *
        ∫⁻ x in {x | t / 2 < f x}, ENNReal.ofReal
          (f x * (Real.log (Real.exp 1 + 2 * f x / t)) ^ k) ∂mu)) =
      ENNReal.ofReal (2 * A) * ∫⁻ x, ENNReal.ofReal (f x) *
        ∫⁻ t in Ioo (0 : ℝ) (2 * f x), ENNReal.ofReal
          (t ^ (p - 2) * (Real.log (Real.exp 1 + 2 * f x / t)) ^ k) ∂volume ∂mu := by
  let K (t : ℝ) (x : X) : ℝ≥0∞ :=
    ENNReal.ofReal (f x) * (Iio (2 * f x)).indicator
      (fun u : ℝ => ENNReal.ofReal
        (u ^ (p - 2) * (Real.log (Real.exp 1 + 2 * f x / u)) ^ k)) t
  have hK : Measurable (Function.uncurry K) := by
    have heq : Function.uncurry K =
        {z : ℝ × X | z.1 < 2 * f z.2}.indicator (fun z =>
          ENNReal.ofReal (f z.2) * ENNReal.ofReal
            (z.1 ^ (p - 2) * (Real.log (Real.exp 1 + 2 * f z.2 / z.1)) ^ k)) := by
      funext z
      by_cases hz : z.1 < 2 * f z.2 <;> simp [K, Function.uncurry_def, hz]
    rw [heq]
    apply Measurable.indicator
    · fun_prop
    · exact measurableSet_lt measurable_fst (measurable_const.mul (hm.comp measurable_snd))
  have hrow (t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal (t ^ (p - 1)) *
        (ENNReal.ofReal (2 * A / t) *
          ∫⁻ x in {x | t / 2 < f x}, ENNReal.ofReal
            (f x * (Real.log (Real.exp 1 + 2 * f x / t)) ^ k) ∂mu) =
        ENNReal.ofReal (2 * A) * ∫⁻ x, K t x ∂mu := by
    rw [← lintegral_indicator (measurableSet_lt measurable_const hm),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro x
    by_cases hx : t / 2 < f x
    · have hx' : t < 2 * f x := by linarith
      simp only [K, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Iio,
        ite_eq_left hx, ite_eq_left hx']
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * A / t),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le (p - 1)),
        ← ENNReal.ofReal_mul (hn x),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * A)]
      congr 1
      have hp : t ^ (p - 1) / t = t ^ (p - 2) := by
        calc
          _ = t ^ (p - 1) / t ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = t ^ ((p - 1) - 1) := (Real.rpow_sub ht _ _).symm
          _ = t ^ (p - 2) := by congr 1; ring
      calc
        _ = (2 * A) * (f x * ((t ^ (p - 1) / t) *
            (Real.log (Real.exp 1 + 2 * f x / t)) ^ k)) := by ring
        _ = _ := by rw [hp]
    · have hx' : ¬ t < 2 * f x := by linarith
      simp only [K, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Iio,
        ite_eq_right hx, ite_eq_right hx', mul_zero]
  have hcolumn (x : X) :
      (∫⁻ t in Ioi (0 : ℝ), K t x) = ENNReal.ofReal (f x) *
        ∫⁻ t in Ioo (0 : ℝ) (2 * f x), ENNReal.ofReal
          (t ^ (p - 2) * (Real.log (Real.exp 1 + 2 * f x / t)) ^ k) := by
    dsimp only [K]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      setLIntegral_indicator measurableSet_Iio]
    rw [show Iio (2 * f x) ∩ Ioi (0 : ℝ) = Ioo 0 (2 * f x) by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo]
      exact and_comm]
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (2 * A) * ∫⁻ x, K t x ∂mu := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hrow t ht
    _ = ENNReal.ofReal (2 * A) * ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, K t x ∂mu :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (2 * A) * ∫⁻ x, ∫⁻ t in Ioi (0 : ℝ), K t x ∂volume ∂mu := by
      rw [lintegral_lintegral_swap hK.aemeasurable]
    _ = _ := by simp_rw [hcolumn]

/-- Layer cake and the truncated endpoint distribution give the
one-dimensional kernel before any scalar kernel estimate is inserted. -/
theorem lintegral_rpow_le_endpoint_kernel
    {X : Type} [MeasurableSpace X] (mu : Measure X) [SFinite mu]
    (f F : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (k : ℕ) (p A : ℝ) (hp : 0 < p) (hA : 0 ≤ A)
    (hlevel : ∀ t : ℝ, 0 < t →
      mu {x | t < F x} ≤ ENNReal.ofReal (2 * A / t) *
        ∫⁻ x in {x | t / 2 < f x}, ENNReal.ofReal
          (f x * (Real.log (Real.exp 1 + 2 * f x / t)) ^ k) ∂mu) :
    (∫⁻ x, ENNReal.ofReal (F x ^ p) ∂mu) ≤
      ENNReal.ofReal (2 * A * p) * ∫⁻ x, ENNReal.ofReal (f x) *
        ∫⁻ t in Ioo (0 : ℝ) (2 * f x), ENNReal.ofReal
          (t ^ (p - 2) * (Real.log (Real.exp 1 + 2 * f x / t)) ^ k) ∂volume ∂mu := by
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul mu
    (Filter.Eventually.of_forall hF0) hF.aemeasurable hp]
  calc
    _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ (p - 1)) *
          (ENNReal.ofReal (2 * A / t) *
            ∫⁻ x in {x | t / 2 < f x}, ENNReal.ofReal
              (f x * (Real.log (Real.exp 1 + 2 * f x / t)) ^ k) ∂mu) := by
      apply mul_le_mul_right
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simpa only [mul_comm] using mul_le_mul_left (hlevel t ht)
        (ENNReal.ofReal (t ^ (p - 1)))
    _ = _ := by
      rw [endpoint_truncated_moment_swap mu f hf hf0 k p A hA,
        ← mul_assoc, ← ENNReal.ofReal_mul hp.le]
      congr 2
      ring

end ReyZygmund
