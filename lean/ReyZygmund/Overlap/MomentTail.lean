import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # The tail estimate obtained from a real moment

This records the Chebyshev step separately from exponential-series arguments.
The moment order is real and the normalized measure may be zero or infinite.
-/

open MeasureTheory
open scoped ENNReal

namespace ReyZygmund.Overlap

/-- A q-th moment bound gives the exact exponential gain obtained by testing
at `exp(b)` times the q-th moment scale. -/
theorem real_moment_tail
    {X : Type} [MeasurableSpace X] (mu : Measure X)
    (H : X → ℝ) (hm : Measurable H) (_hn : ∀ x, 0 ≤ H x)
    (q M b : ℝ) (hq : 0 < q) (hM : 0 < M)
    (hbound : (∫⁻ x, ENNReal.ofReal (H x ^ q) ∂mu) ≤
      ENNReal.ofReal (M ^ q) * mu Set.univ) :
    mu {x | Real.exp b * M < H x} ≤
      ENNReal.ofReal (Real.exp (-b * q)) * mu Set.univ := by
  have ht : 0 < (Real.exp b * M) ^ q :=
    Real.rpow_pos_of_pos (mul_pos (Real.exp_pos b) hM) q
  have hsub : {x | Real.exp b * M < H x} ⊆
      {x | ENNReal.ofReal ((Real.exp b * M) ^ q) ≤ ENNReal.ofReal (H x ^ q)} := by
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    exact (Real.rpow_lt_rpow (by positivity) hx hq).le
  have hmeas : Measurable (fun x => ENNReal.ofReal (H x ^ q)) := by fun_prop
  have hratio : M ^ q / (Real.exp b * M) ^ q = Real.exp (-b * q) := by
    rw [Real.mul_rpow (Real.exp_pos b).le hM.le, ← Real.exp_mul]
    have hp : M ^ q ≠ 0 := (Real.rpow_pos_of_pos hM q).ne'
    calc
      M ^ q / (Real.exp (b * q) * M ^ q) = 1 / Real.exp (b * q) := by
        field_simp [hp]
      _ = Real.exp (-b * q) := by
        rw [one_div, ← Real.exp_neg]
        congr 1
        ring
  calc
    _ ≤ mu {x | ENNReal.ofReal ((Real.exp b * M) ^ q) ≤
        ENNReal.ofReal (H x ^ q)} := measure_mono hsub
    _ ≤ (∫⁻ x, ENNReal.ofReal (H x ^ q) ∂mu) /
        ENNReal.ofReal ((Real.exp b * M) ^ q) :=
      meas_ge_le_lintegral_div hmeas.aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr ht) ENNReal.ofReal_ne_top
    _ ≤ (ENNReal.ofReal (M ^ q) * mu Set.univ) /
        ENNReal.ofReal ((Real.exp b * M) ^ q) := ENNReal.div_le_div_right hbound _
    _ = _ := by
      rw [mul_comm _ (mu Set.univ), mul_div_assoc,
        ← ENNReal.ofReal_div_of_pos ht, hratio, mul_comm]

/-- For every nonnegative u the normalized polynomial threshold has an
exponential tail. Small u uses only the total measure; u at least two uses
the moment of order u. -/
theorem polynomial_moments_tail
    {X : Type} [MeasurableSpace X] (mu : Measure X)
    (H : X → ℝ) (hm : Measurable H) (hn : ∀ x, 0 ≤ H x)
    (k : ℕ) (C : ℝ) (hC : 0 < C)
    (hmom : ∀ q : ℝ, 2 ≤ q →
      (∫⁻ x, ENNReal.ofReal (H x ^ q) ∂mu) ≤
        ENNReal.ofReal ((C * q ^ k) ^ q) * mu Set.univ)
    (u : ℝ) (_hu : 0 ≤ u) :
    mu {x | Real.exp 2 * C * u ^ k < H x} ≤
      ENNReal.ofReal (Real.exp 4 * Real.exp (-2 * u)) * mu Set.univ := by
  by_cases hu2 : 2 ≤ u
  · have hu0 : 0 < u := by linarith
    have h := real_moment_tail mu H hm hn u (C * u ^ k) 2 hu0
      (mul_pos hC (pow_pos hu0 _)) (hmom u hu2)
    have he : Real.exp (-2 * u) ≤ Real.exp 4 * Real.exp (-2 * u) := by
      exact le_mul_of_one_le_left (Real.exp_nonneg _) (Real.one_le_exp (by norm_num))
    simpa only [mul_assoc] using h.trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal he) (mu Set.univ))
  · have he : 1 ≤ Real.exp 4 * Real.exp (-2 * u) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    calc
      _ ≤ mu Set.univ := measure_mono (Set.subset_univ _)
      _ = (1 : ℝ≥0∞) * mu Set.univ := (one_mul _).symm
      _ ≤ _ := mul_le_mul_left (by simpa using ENNReal.ofReal_le_ofReal he) _

end ReyZygmund.Overlap
