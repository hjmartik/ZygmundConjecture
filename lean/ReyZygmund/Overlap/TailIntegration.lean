import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Integrating an exponential tail

The conclusion concerns the excess exponential. The proof uses the layer-cake
identity and evaluates the convergent scalar integral, including the zero
measure and zero tail-constant cases.
-/

open MeasureTheory Set
open scoped ENNReal

namespace ReyZygmund.Overlap

/-- An exponential tail gives the exact excess-exponential coefficient for
every strictly smaller positive exponent. -/
theorem exponential_tail_lintegral
    {X : Type} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (Y : X → ℝ) (hm : Measurable Y) (hn : ∀ x, 0 ≤ Y x)
    (C a c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) (hca : c < a)
    (htail : ∀ t : ℝ, 0 ≤ t →
      mu {x | t < Y x} ≤ ENNReal.ofReal (C * Real.exp (-a * t)) * mu univ) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (c * Y x) - 1) ∂mu) ≤
      ENNReal.ofReal (C * c / (a - c)) * mu univ := by
  have hint (t : ℝ) :
      IntervalIntegrable (fun u : ℝ => c * Real.exp (c * u)) volume 0 t := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hprimitive (t : ℝ) :
      (∫ u in (0 : ℝ)..t, c * Real.exp (c * u)) = Real.exp (c * t) - 1 := by
    have hd (u : ℝ) : HasDerivAt (fun v : ℝ => Real.exp (c * v))
        (c * Real.exp (c * u)) u := by
      simpa only [id_eq, mul_one, mul_comm] using ((hasDerivAt_id u).const_mul c).exp
    convert intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hd u) (hint t)
    simp
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul mu
    (Filter.Eventually.of_forall hn) hm.aemeasurable
    (fun t _ => hint t)
    (Filter.Eventually.of_forall (fun t => mul_nonneg hc.le (Real.exp_nonneg (c * t))))
  simp only [hprimitive] at hlayer
  rw [hlayer]
  have hscalar :
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (C * c * Real.exp ((c - a) * t))) =
        ENNReal.ofReal (C * c / (a - c)) := by
    have hi := (integrableOn_exp_mul_Ioi (sub_neg.mpr hca) 0).const_mul (C * c)
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun t => by positivity))]
    rw [integral_const_mul, integral_exp_mul_Ioi (sub_neg.mpr hca) 0]
    congr 1
    simp only [mul_zero, Real.exp_zero]
    rw [show c - a = -(a - c) by ring, neg_div_neg_eq]
    ring
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (C * c * Real.exp ((c - a) * t)) * mu univ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      calc
        _ ≤ (ENNReal.ofReal (C * Real.exp (-a * t)) * mu univ) *
            ENNReal.ofReal (c * Real.exp (c * t)) :=
          mul_le_mul_left (htail t ht.le) _
        _ = _ := by
          rw [mul_right_comm, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          rw [show (C * Real.exp (-a * t)) * (c * Real.exp (c * t)) =
            C * c * (Real.exp (-a * t) * Real.exp (c * t)) by ring,
            ← Real.exp_add]
          congr 2
          ring
    _ = _ := by
      rw [lintegral_mul_const' _ _ (measure_ne_top mu univ), hscalar]

end ReyZygmund.Overlap
