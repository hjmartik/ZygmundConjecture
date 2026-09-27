import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The scalar logarithmic kernel in the endpoint-to-strong estimate

The Gamma integral is first shown integrable. Translation then gives
the exact `exp 2 * k!` coefficient, with no assumed convergence of the
logarithmic kernel. The final exponential substitution is a Lebesgue
change-of-variables identity.
-/

open MeasureTheory Set
open scoped ENNReal

namespace ReyZygmund

private theorem log_exp_add_exp_bounds (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ Real.log (Real.exp 1 + Real.exp t) ∧
      Real.log (Real.exp 1 + Real.exp t) ≤ t + 2 := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have het : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  have he2 : Real.exp 1 + 1 ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  refine ⟨Real.log_nonneg (by linarith [Real.exp_pos t]), ?_⟩
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    Real.exp 1 + Real.exp t ≤ (Real.exp 1 + 1) * Real.exp t := by
      nlinarith [mul_nonneg (Real.exp_pos 1).le (sub_nonneg.mpr het)]
    _ ≤ Real.exp 2 * Real.exp t :=
      mul_le_mul_of_nonneg_right he2 (Real.exp_pos t).le
    _ = Real.exp (t + 2) := by rw [← Real.exp_add]; congr 1; ring

private theorem integrable_exp_neg_mul_pow (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => Real.exp (-(ε * t)) * t ^ k) (Ioi 0) := by
  have hbase : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ k) (Ioi 0) := by
    simpa only [add_sub_cancel_right, Real.rpow_natCast] using
      Real.GammaIntegral_convergent (s := (k : ℝ) + 1) (by positivity)
  have hscaled :
      IntegrableOn (fun t : ℝ => Real.exp (-(ε * t)) * (ε * t) ^ k) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun t : ℝ => Real.exp (-t) * t ^ k) 0 hε).mpr
    simpa only [mul_zero] using hbase
  refine (hscaled.div_const (ε ^ k)).congr ?_
  filter_upwards with t
  rw [mul_pow]
  field_simp [hε.ne']

private theorem integral_exp_neg_mul_pow (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (∫ t : ℝ in Ioi 0, Real.exp (-(ε * t)) * t ^ k) =
      (k.factorial : ℝ) / ε ^ (k + 1) := by
  calc
    (∫ t : ℝ in Ioi 0, Real.exp (-(ε * t)) * t ^ k) =
        ∫ t : ℝ in Ioi 0,
          t ^ (((k + 1 : ℕ) : ℝ) - 1) * Real.exp (-(ε * t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Real.rpow_natCast]
      ring
    _ = (1 / ε) ^ ((k + 1 : ℕ) : ℝ) * Real.Gamma ((k + 1 : ℕ) : ℝ) :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hε
    _ = (k.factorial : ℝ) / ε ^ (k + 1) := by
      rw [Real.rpow_natCast, Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial]
      simp [div_eq_mul_inv, mul_comm]

private theorem lintegral_exp_neg_mul_pow (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-(ε * t)) * t ^ k)) =
      ENNReal.ofReal ((k.factorial : ℝ) / ε ^ (k + 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_neg_mul_pow k ε hε), integral_exp_neg_mul_pow k ε hε]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (Real.exp_pos _).le (pow_nonneg ht.le _)

private theorem lintegral_exp_shift_pow (k : ℕ) (ε : ℝ) :
    (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-(ε * t)) * (t + 2) ^ k)) =
      ENNReal.ofReal (Real.exp (2 * ε)) *
        ∫⁻ u : ℝ in Ioi 2, ENNReal.ofReal (Real.exp (-(ε * u)) * u ^ k) := by
  have himage : (fun t : ℝ => t + 2) '' Ioi 0 = Ioi 2 := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact show 2 < t + 2 by linarith [mem_Ioi.mp ht]
    · intro hu
      exact ⟨u - 2, by change 0 < u - 2; linarith [mem_Ioi.mp hu], by ring⟩
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul
    (s := Ioi (0 : ℝ)) (f := fun t : ℝ => t + 2) (f' := fun _ => 1) measurableSet_Ioi
    (fun t _ => ((hasDerivAt_id t).add_const 2).hasDerivWithinAt)
    (fun _ _ _ _ h => add_right_cancel h)
    (fun u : ℝ => ENNReal.ofReal (Real.exp (-(ε * u)) * u ^ k))
  rw [himage] at hchange
  simp only [abs_one, ENNReal.ofReal_one, one_mul] at hchange
  calc
    (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-(ε * t)) * (t + 2) ^ k)) =
        ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (2 * ε)) *
          ENNReal.ofReal (Real.exp (-(ε * (t + 2))) * (t + 2) ^ k) := by
      apply lintegral_congr
      intro t
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ = ENNReal.ofReal (Real.exp (2 * ε)) *
        ∫⁻ t : ℝ in Ioi 0,
          ENNReal.ofReal (Real.exp (-(ε * (t + 2))) * (t + 2) ^ k) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.exp (2 * ε)) *
        ∫⁻ u : ℝ in Ioi 2, ENNReal.ofReal (Real.exp (-(ε * u)) * u ^ k) := by
      rw [← hchange]

/-- The exact logarithmic-exponential kernel estimate, including `k = 0` and
the endpoint `ε = 1`. No convergence hypothesis is imposed. -/
theorem endpoint_log_exp_kernel (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫⁻ t : ℝ in Ioi 0,
      ENNReal.ofReal (Real.exp (-ε * t) * (Real.log (Real.exp 1 + Real.exp t)) ^ k)) ≤
      ENNReal.ofReal (Real.exp 2 * (k.factorial : ℝ) / ε ^ (k + 1)) := by
  calc
    (∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal (Real.exp (-ε * t) * (Real.log (Real.exp 1 + Real.exp t)) ^ k)) ≤
        ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-(ε * t)) * (t + 2) ^ k) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      apply ENNReal.ofReal_le_ofReal
      rw [neg_mul]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (log_exp_add_exp_bounds t ht.le).1
          (log_exp_add_exp_bounds t ht.le).2 k) (Real.exp_pos _).le
    _ = ENNReal.ofReal (Real.exp (2 * ε)) *
        ∫⁻ u : ℝ in Ioi 2, ENNReal.ofReal (Real.exp (-(ε * u)) * u ^ k) :=
      lintegral_exp_shift_pow k ε
    _ ≤ ENNReal.ofReal (Real.exp 2) *
        ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-(ε * u)) * u ^ k) := by
      apply mul_le_mul
      · exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
      · exact lintegral_mono_set (show Ioi (2 : ℝ) ⊆ Ioi 0 from
          fun _ hu => lt_trans (show (0 : ℝ) < 2 by norm_num) hu)
      · exact zero_le
      · exact zero_le
    _ = ENNReal.ofReal (Real.exp 2 * (k.factorial : ℝ) / ε ^ (k + 1)) := by
      rw [lintegral_exp_neg_mul_pow k ε hε,
        ← ENNReal.ofReal_mul (Real.exp_pos 2).le]
      congr 1
      ring

private theorem exp_substitution_image (A : ℝ) (hA : 0 < A) :
    (fun u : ℝ => A * Real.exp (-u)) '' Ioi 0 = Ioo 0 A := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨mul_pos hA (Real.exp_pos _), ?_⟩
    simpa only [mul_one] using mul_lt_mul_of_pos_left
      (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mem_Ioi.mp hu))) hA
  · intro ht
    have hratio : 0 < t / A := div_pos ht.1 hA
    have hlog : Real.log (t / A) < 0 :=
      Real.log_neg hratio ((div_lt_one hA).mpr ht.2)
    refine ⟨-Real.log (t / A), neg_pos.mpr hlog, ?_⟩
    dsimp only
    rw [neg_neg, Real.exp_log hratio]
    field_simp [hA.ne']

private theorem exp_substitution_power (A p u : ℝ) (hA : 0 < A) :
    (A * Real.exp (-u)) * Real.rpow (A * Real.exp (-u)) (p - 2) =
      Real.rpow A (p - 1) * Real.exp (-(p - 1) * u) := by
  have hx : 0 < A * Real.exp (-u) := mul_pos hA (Real.exp_pos _)
  simp only [Real.rpow_eq_pow]
  calc
    (A * Real.exp (-u)) * (A * Real.exp (-u)) ^ (p - 2) =
        (A * Real.exp (-u)) ^ (p - 1) := by
      rw [show p - 1 = 1 + (p - 2) by ring, Real.rpow_add hx, Real.rpow_one]
    _ = A ^ (p - 1) * (Real.exp (-u)) ^ (p - 1) :=
      Real.mul_rpow hA.le (Real.exp_pos _).le
    _ = A ^ (p - 1) * Real.exp (-(p - 1) * u) := by
      rw [← Real.exp_mul]
      congr 2
      ring

private theorem exp_substitution_kernel (k : ℕ) (p A : ℝ) (hA : 0 < A) :
    (∫⁻ t : ℝ in Ioo 0 A,
      ENNReal.ofReal (Real.rpow t (p - 2) * (Real.log (Real.exp 1 + A / t)) ^ k)) =
      ENNReal.ofReal (Real.rpow A (p - 1)) *
        ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal
          (Real.exp (-(p - 1) * u) * (Real.log (Real.exp 1 + Real.exp u)) ^ k) := by
  have hderiv (u : ℝ) :
      HasDerivAt (fun t : ℝ => A * Real.exp (-t)) (-(A * Real.exp (-u))) u := by
    simpa only [id_eq, Pi.neg_apply, mul_neg, mul_one] using
      ((hasDerivAt_id u).neg.exp.const_mul A)
  have hinj : InjOn (fun u : ℝ => A * Real.exp (-u)) (Ioi 0) := by
    intro u _ v _ huv
    have he : Real.exp (-u) = Real.exp (-v) := mul_left_cancel₀ hA.ne' huv
    exact neg_injective (Real.exp_injective he)
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul
    (s := Ioi (0 : ℝ)) (f := fun u : ℝ => A * Real.exp (-u))
    (f' := fun u => -(A * Real.exp (-u)))
    measurableSet_Ioi (fun u _ => (hderiv u).hasDerivWithinAt) hinj
    (fun t : ℝ => ENNReal.ofReal
      (Real.rpow t (p - 2) * (Real.log (Real.exp 1 + A / t)) ^ k))
  rw [exp_substitution_image A hA] at hchange
  rw [hchange, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro u
  simp only [Real.rpow_eq_pow]
  have hx : 0 < A * Real.exp (-u) := mul_pos hA (Real.exp_pos _)
  have hratio : A / (A * Real.exp (-u)) = Real.exp u := by
    rw [Real.exp_neg]
    field_simp [hA.ne']
  rw [abs_neg, abs_of_pos hx, ← ENNReal.ofReal_mul hx.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hA.le (p - 1))]
  congr 1
  have hpower := exp_substitution_power A p u hA
  simp only [Real.rpow_eq_pow] at hpower
  rw [hratio, ← mul_assoc, hpower]
  ring

/-- The inner scalar kernel in the truncated endpoint-to-strong calculation.
The integration interval is `Ioo 0 (2*a)`, including its empty
case when `a = 0`. All powers of the integration variable are real powers. -/
theorem endpoint_truncated_log_kernel (k : ℕ) (p a : ℝ)
    (hp : 1 < p) (hp2 : p ≤ 2) (ha : 0 ≤ a) :
    (∫⁻ t : ℝ in Ioo 0 (2 * a),
      ENNReal.ofReal (Real.rpow t (p - 2) *
        (Real.log (Real.exp 1 + 2 * a / t)) ^ k)) ≤
      ENNReal.ofReal (Real.rpow (2 * a) (p - 1) * Real.exp 2 *
        (k.factorial : ℝ) / (p - 1) ^ (k + 1)) := by
  simp only [Real.rpow_eq_pow]
  by_cases ha0 : a = 0
  · simp [ha0, Real.zero_rpow (by linarith : p - 1 ≠ 0)]
  have hA : 0 < 2 * a := mul_pos (by norm_num) (lt_of_le_of_ne ha (Ne.symm ha0))
  have hε : 0 < p - 1 := by linarith
  have hε1 : p - 1 ≤ 1 := by linarith
  have hsub := exp_substitution_kernel k p (2 * a) hA
  simp only [Real.rpow_eq_pow] at hsub
  rw [hsub]
  calc
    ENNReal.ofReal ((2 * a) ^ (p - 1)) *
        (∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal
          (Real.exp (-(p - 1) * u) * (Real.log (Real.exp 1 + Real.exp u)) ^ k)) ≤
        ENNReal.ofReal ((2 * a) ^ (p - 1)) *
          ENNReal.ofReal (Real.exp 2 * (k.factorial : ℝ) / (p - 1) ^ (k + 1)) :=
      mul_le_mul le_rfl (endpoint_log_exp_kernel k (p - 1) hε hε1)
        zero_le zero_le
    _ = ENNReal.ofReal ((2 * a) ^ (p - 1) * Real.exp 2 *
        (k.factorial : ℝ) / (p - 1) ^ (k + 1)) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hA.le (p - 1))]
      congr 1
      ring

end ReyZygmund
