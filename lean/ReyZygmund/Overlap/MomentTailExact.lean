import ReyZygmund.Overlap.MomentTail
import ReyZygmund.Overlap.TailIntegration
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The exponential constant in the endpoint-to-overlap argument

Moment estimates down to order one give a tail bound starting at one. Subtracting
this threshold reduces the exponential integral to the exponential-tail formula,
retaining the quantitative coefficient and bound.
-/

open MeasureTheory Set
open scoped ENNReal

namespace ReyZygmund.Overlap

/-- Integrating a unit exponential tail starting at one costs at most three
times the total measure. No tail assumption is needed below one. -/
theorem exponential_tail_from_one
    {X : Type} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (Y : X → ℝ) (hm : Measurable Y) (_hn : ∀ x, 0 ≤ Y x)
    (htail : ∀ t : ℝ, 1 ≤ t →
      mu {x | t < Y x} ≤ ENNReal.ofReal (Real.exp (-t)) * mu univ) :
    (∫⁻ x, ENNReal.ofReal (Real.exp ((1 / 2 : ℝ) * Y x)) ∂mu) ≤ 3 * mu univ := by
  let Z := fun x => max (Y x - 1) 0
  have hZ : Measurable Z := (hm.sub measurable_const).max measurable_const
  have hZ0 : ∀ x, 0 ≤ Z x := fun x => le_max_right _ _
  have hZtail (t : ℝ) (ht : 0 ≤ t) :
      mu {x | t < Z x} ≤
        ENNReal.ofReal (Real.exp (-1) * Real.exp (-(1 : ℝ) * t)) * mu univ := by
    have hsub : {x | t < Z x} ⊆ {x | t + 1 < Y x} := by
      intro x hx
      change t < max (Y x - 1) 0 at hx
      change t + 1 < Y x
      rcases lt_max_iff.mp hx with hx | hx
      · linarith
      · exact (not_lt_of_ge ht hx).elim
    have he : Real.exp (-(t + 1)) = Real.exp (-1) * Real.exp (-(1 : ℝ) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simpa only [he] using (measure_mono hsub).trans (htail (t + 1) (by linarith))
  have hZint := exponential_tail_lintegral mu Z hZ hZ0
    (Real.exp (-1)) 1 (1 / 2) (Real.exp_nonneg _) (by norm_num) (by norm_num) hZtail
  have hc : Real.exp (-1) * (1 / 2 : ℝ) / (1 - 1 / 2) = Real.exp (-1) := by ring
  rw [hc] at hZint
  have hpoint (x : X) : Real.exp ((1 / 2 : ℝ) * Y x) ≤
      Real.exp (1 / 2) * (1 + (Real.exp ((1 / 2 : ℝ) * Z x) - 1)) := by
    have hYZ : Y x ≤ 1 + Z x := by dsimp [Z]; linarith [le_max_left (Y x - 1) 0]
    have hh := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hYZ (by norm_num : (0 : ℝ) ≤ 1 / 2))
    convert hh using 1
    rw [show (1 / 2 : ℝ) * (1 + Z x) = 1 / 2 + (1 / 2 : ℝ) * Z x by ring,
      Real.exp_add]
    ring
  have hnonneg (x : X) : 0 ≤ Real.exp ((1 / 2 : ℝ) * Z x) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (mul_nonneg (by norm_num) (hZ0 x)))
  have hcoeff : Real.exp (1 / 2 : ℝ) * (1 + Real.exp (-1)) ≤ 3 := by
    have hs : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
      rw [pow_two, ← Real.exp_add]
      norm_num
    have he2 : Real.exp (1 / 2 : ℝ) < 2 := by
      nlinarith [Real.exp_pos (1 / 2 : ℝ), Real.exp_one_lt_three]
    have hen : Real.exp (-(1 / 2 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have he : Real.exp (1 / 2 : ℝ) * (1 + Real.exp (-1)) =
        Real.exp (1 / 2 : ℝ) + Real.exp (-(1 / 2 : ℝ)) := by
      rw [mul_add, mul_one, ← Real.exp_add]
      norm_num
    rw [he]
    linarith
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
        (1 + ENNReal.ofReal (Real.exp ((1 / 2 : ℝ) * Z x) - 1)) ∂mu := by
      apply lintegral_mono
      intro x
      have hh := ENNReal.ofReal_le_ofReal (hpoint x)
      rwa [ENNReal.ofReal_mul (Real.exp_nonneg _),
        ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) (hnonneg x), ENNReal.ofReal_one] at hh
    _ = ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
        (mu univ + ∫⁻ x, ENNReal.ofReal (Real.exp ((1 / 2 : ℝ) * Z x) - 1) ∂mu) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left measurable_const]
      simp only [lintegral_const, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
        (mu univ + ENNReal.ofReal (Real.exp (-1)) * mu univ) :=
      mul_le_mul_right (add_le_add_right hZint _) _
    _ = ENNReal.ofReal (Real.exp (1 / 2 : ℝ) * (1 + Real.exp (-1))) * mu univ := by
      rw [ENNReal.ofReal_mul (Real.exp_nonneg _),
        ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) (Real.exp_nonneg _),
        ENNReal.ofReal_one, mul_assoc, add_mul, one_mul]
    _ ≤ _ := mul_le_mul_left (by simpa using ENNReal.ofReal_le_ofReal hcoeff) _

/-- The complete real-moment scale, including orders between one and two,
gives the precise normalized exponential in the admitted support lemma. -/
theorem all_polynomial_moments_exponential
    {X : Type} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (H : X → ℝ) (hm : Measurable H) (hn : ∀ x, 0 ≤ H x)
    (k : ℕ) (hk : 1 ≤ k) (C : ℝ) (hC : 0 < C)
    (hmom : ∀ q : ℝ, 1 ≤ q →
      (∫⁻ x, ENNReal.ofReal (H x ^ q) ∂mu) ≤
        ENNReal.ofReal ((C * q ^ k) ^ q) * mu univ) :
    (∫⁻ x, ENNReal.ofReal
      (Real.exp ((1 / 2 : ℝ) * (H x / (Real.exp 1 * C)) ^ (1 / (k : ℝ)))) ∂mu) ≤
        3 * mu univ := by
  let Y := fun x => (H x / (Real.exp 1 * C)) ^ (1 / (k : ℝ))
  have hden : 0 < Real.exp 1 * C := mul_pos (Real.exp_pos _) hC
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hY : Measurable Y := by dsimp [Y]; fun_prop
  have hY0 : ∀ x, 0 ≤ Y x := fun x => Real.rpow_nonneg (div_nonneg (hn x) hden.le) _
  have hpow (x : X) : Y x ^ k = H x / (Real.exp 1 * C) := by
    dsimp [Y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg (hn x) hden.le),
      one_div_mul_cancel hk0, Real.rpow_one]
  apply exponential_tail_from_one mu Y hY hY0
  intro u hu
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have htail := real_moment_tail mu H hm hn u (C * u ^ k) 1 hu0
    (mul_pos hC (pow_pos hu0 _)) (hmom u hu)
  have hsub : {x | u < Y x} ⊆ {x | Real.exp 1 * (C * u ^ k) < H x} := by
    intro x hx
    have hh : u ^ k < Y x ^ k := pow_lt_pow_left₀ hx hu0.le (by omega)
    rw [hpow x] at hh
    have hh' := (lt_div_iff₀ hden).mp hh
    change Real.exp 1 * (C * u ^ k) < H x
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh'
  simpa only [neg_one_mul] using (measure_mono hsub).trans htail

end ReyZygmund.Overlap
