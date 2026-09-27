import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # From moment growth to exponential integrability

The positive exponential series turns the polynomial moment bounds into the
sparse-overlap exponential estimate. This measure-theoretic argument does not
require a geometric maximal theorem or the intermediate tail estimate used in the
paper.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace ReyZygmund.Overlap

private theorem small_power_le (x q : ℝ) (hx : 0 ≤ x)
    (hq : 0 ≤ q) (hq2 : q ≤ 2) : Real.rpow x q ≤ 1 + x ^ 2 := by
  by_cases hx1 : x ≤ 1
  · have h := Real.rpow_le_one hx hx1 hq
    have hs := sq_nonneg x
    simpa only [Real.rpow_eq_pow] using (h.trans (by linarith))
  · have h := Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hx1)) hq2
    have h' : Real.rpow x q ≤ x ^ 2 := by simpa using h
    linarith

private theorem root_power (x : ℝ) (hx : 0 ≤ x) (k n : ℕ) :
    (Real.rpow x (1 / (k : ℝ))) ^ n = Real.rpow x ((n : ℝ) / (k : ℝ)) := by
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul_natCast hx]
  congr 1
  ring

private theorem ofReal_exp_eq_tsum (t : ℝ) (ht : 0 ≤ t) :
    ENNReal.ofReal (Real.exp t) =
      ∑' n : ℕ, ENNReal.ofReal (t ^ n / (n.factorial : ℝ)) := by
  have hs : HasSum (fun n : ℕ => t ^ n / (n.factorial : ℝ)) (Real.exp t) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp t
  simpa only [hs.tsum_eq] using ENNReal.ofReal_tsum_of_nonneg
    (fun n : ℕ => div_nonneg (pow_nonneg ht n) (Nat.cast_nonneg _)) hs.summable

private theorem large_moment_le (k n : ℕ) (hk : 1 ≤ k)
    (C q : ℝ) (hC : 0 < C) (hq : 2 ≤ q) (hqn : (k : ℝ) * q = n) :
    (C * q ^ k) ^ q ≤ ((C + 1) * (n : ℝ)) ^ n := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq0 : 0 ≤ q := by linarith
  have hqn' : q ≤ n := by nlinarith
  have hCq : C ^ q ≤ (C + 1) ^ n := by
    have h₁ := Real.rpow_le_rpow hC.le (by linarith : C ≤ C + 1) hq0
    have h₂ := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ C + 1) hqn'
    exact h₁.trans (by simpa using h₂)
  calc
    (C * q ^ k) ^ q = C ^ q * q ^ n := by
      rw [Real.mul_rpow hC.le (pow_nonneg hq0 k),
        ← Real.rpow_natCast_mul hq0, hqn, Real.rpow_natCast]
    _ ≤ (C + 1) ^ n * (n : ℝ) ^ n :=
      mul_le_mul hCq (pow_le_pow_left₀ hq0 hqn' n)
        (pow_nonneg hq0 n) (pow_nonneg (by linarith) n)
    _ = ((C + 1) * (n : ℝ)) ^ n := (mul_pow _ _ _).symm

private theorem factorial_geometric_bound (c A : ℝ) (hc : 0 ≤ c) (hA : 0 ≤ A)
    (hscale : c * A * Real.exp 1 ≤ 1 / 2) (n : ℕ) :
    (c ^ n / (n.factorial : ℝ)) * (A * (n : ℝ)) ^ n ≤ (1 / 2 : ℝ) ^ n := by
  calc
    _ = (c * A) ^ n * ((n : ℝ) ^ n / (n.factorial : ℝ)) := by
      rw [mul_pow, mul_pow]
      ring
    _ ≤ (c * A) ^ n * Real.exp (n : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n)
        (pow_nonneg (mul_nonneg hc hA) n)
    _ = (c * A) ^ n * (Real.exp 1) ^ n := by rw [Real.exp_one_pow]
    _ = (c * A * Real.exp 1) ^ n := (mul_pow _ _ _).symm
    _ ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_left₀ (mul_nonneg (mul_nonneg hc hA) (Real.exp_nonneg _)) hscale n

private theorem small_coefficient_bound (c L : ℝ) (hc : 0 ≤ c)
    (hc2 : c ≤ 1 / 2) (hL : 0 ≤ L) (n : ℕ) :
    (c ^ n / (n.factorial : ℝ)) * L ≤ L * (1 / 2 : ℝ) ^ n := by
  have hfac : (1 : ℝ) ≤ n.factorial := by
    exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos n)
  have h := (div_le_self (pow_nonneg hc n) hfac).trans (pow_le_pow_left₀ hc hc2 n)
  simpa only [mul_comm L] using mul_le_mul_of_nonneg_right h hL

private theorem small_moment_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (H : α → ℝ) (hH : ∀ x, 0 ≤ H x)
    (k : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hsecond : (∫⁻ x, (ENNReal.ofReal (H x)) ^ (2 : ℝ) ∂μ) ≤
      (ENNReal.ofReal (C * (2 : ℝ) ^ k)) ^ (2 : ℝ) * μ Set.univ)
    (q : ℝ) (hq : 0 ≤ q) (hq2 : q ≤ 2) :
    (∫⁻ x, (ENNReal.ofReal (H x)) ^ q ∂μ) ≤
      ENNReal.ofReal (1 + (C * (2 : ℝ) ^ k) ^ 2) * μ Set.univ := by
  have hpoint (x : α) : (ENNReal.ofReal (H x)) ^ q ≤
      1 + (ENNReal.ofReal (H x)) ^ (2 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (hH x) hq]
    calc
      _ ≤ ENNReal.ofReal (1 + (H x) ^ 2) :=
        ENNReal.ofReal_le_ofReal (small_power_le (H x) q (hH x) hq hq2)
      _ = _ := by
        rw [ENNReal.ofReal_add zero_le_one (sq_nonneg _), ENNReal.ofReal_one,
          ENNReal.ofReal_pow (hH x), ENNReal.rpow_two]
  calc
    _ ≤ ∫⁻ x, 1 + (ENNReal.ofReal (H x)) ^ (2 : ℝ) ∂μ := lintegral_mono hpoint
    _ = μ Set.univ + ∫⁻ x, (ENNReal.ofReal (H x)) ^ (2 : ℝ) ∂μ := by
      rw [lintegral_add_left measurable_const]
      simp only [lintegral_const, one_mul]
    _ ≤ μ Set.univ + (ENNReal.ofReal (C * (2 : ℝ) ^ k)) ^ (2 : ℝ) * μ Set.univ :=
      add_le_add le_rfl hsecond
    _ = _ := by
      rw [ENNReal.rpow_two,
        ← ENNReal.ofReal_pow (mul_nonneg hC (pow_nonneg (by norm_num) k)) 2,
        ENNReal.ofReal_add zero_le_one (sq_nonneg _), ENNReal.ofReal_one,
        add_mul, one_mul]

private theorem exponential_term_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (H : α → ℝ) (hH : ∀ x, 0 ≤ H x)
    (k : ℕ) (hk : 1 ≤ k) (C : ℝ) (hC : 0 < C)
    (hmom : ∀ q : ℝ, 2 ≤ q →
      (∫⁻ x, (ENNReal.ofReal (H x)) ^ q ∂μ) ≤
        (ENNReal.ofReal (C * q ^ k)) ^ q * μ Set.univ)
    (c : ℝ) (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2)
    (hscale : c * (C + 1) * Real.exp 1 ≤ 1 / 2) (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal
      ((c * Real.rpow (H x) (1 / (k : ℝ))) ^ n / (n.factorial : ℝ)) ∂μ) ≤
      ENNReal.ofReal ((1 + (C * (2 : ℝ) ^ k) ^ 2) * (1 / 2 : ℝ) ^ n) * μ Set.univ := by
  let q : ℝ := (n : ℝ) / (k : ℝ)
  let a : ℝ := c ^ n / (n.factorial : ℝ)
  let L : ℝ := 1 + (C * (2 : ℝ) ^ k) ^ 2
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (zero_lt_one.trans_le hk)
  have hq0 : 0 ≤ q := div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg k)
  have hqn : (k : ℝ) * q = n := by
    dsimp only [q]
    field_simp
  have ha : 0 ≤ a := div_nonneg (pow_nonneg hc n) (Nat.cast_nonneg _)
  have hL1 : 1 ≤ L := le_add_of_nonneg_right (sq_nonneg _)
  have hL : 0 ≤ L := zero_le_one.trans hL1
  have hpoint (x : α) : ENNReal.ofReal
      ((c * Real.rpow (H x) (1 / (k : ℝ))) ^ n / (n.factorial : ℝ)) =
      ENNReal.ofReal a * (ENNReal.ofReal (H x)) ^ q := by
    rw [ENNReal.ofReal_rpow_of_nonneg (hH x) hq0, ← ENNReal.ofReal_mul ha]
    congr 1
    rw [mul_pow, root_power (H x) (hH x) k n]
    dsimp only [a, q]
    simp only [Real.rpow_eq_pow]
    ring
  rw [lintegral_congr hpoint, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  by_cases hq : 2 ≤ q
  · have hm := hmom q hq
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC.le (pow_nonneg hq0 k)) hq0] at hm
    have hcoeff : a * (C * q ^ k) ^ q ≤ L * (1 / 2 : ℝ) ^ n := by
      calc
        _ ≤ a * ((C + 1) * (n : ℝ)) ^ n :=
          mul_le_mul_of_nonneg_left (large_moment_le k n hk C q hC hq hqn) ha
        _ ≤ (1 / 2 : ℝ) ^ n := factorial_geometric_bound c (C + 1) hc
          (by linarith) hscale n
        _ ≤ L * (1 / 2 : ℝ) ^ n := by
          nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) n]
    calc
      _ ≤ ENNReal.ofReal a * (ENNReal.ofReal ((C * q ^ k) ^ q) * μ Set.univ) :=
        mul_le_mul_right hm _
      _ = ENNReal.ofReal (a * (C * q ^ k) ^ q) * μ Set.univ := by
        rw [ENNReal.ofReal_mul ha, mul_assoc]
      _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal hcoeff) _
  · have hm := small_moment_integral μ H hH k C hC.le
      (hmom 2 (le_refl _)) q hq0 (le_of_lt (lt_of_not_ge hq))
    have hcoeff : a * L ≤ L * (1 / 2 : ℝ) ^ n :=
      small_coefficient_bound c L hc hc2 hL n
    calc
      _ ≤ ENNReal.ofReal a * (ENNReal.ofReal L * μ Set.univ) := mul_le_mul_right hm _
      _ = ENNReal.ofReal (a * L) * μ Set.univ := by
        rw [ENNReal.ofReal_mul ha, mul_assoc]
      _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal hcoeff) _

private theorem exponential_integral_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (H : α → ℝ) (hHm : Measurable H) (hH : ∀ x, 0 ≤ H x)
    (k : ℕ) (hk : 1 ≤ k) (C : ℝ) (hC : 0 < C)
    (hmom : ∀ q : ℝ, 2 ≤ q →
      (∫⁻ x, (ENNReal.ofReal (H x)) ^ q ∂μ) ≤
        (ENNReal.ofReal (C * q ^ k)) ^ q * μ Set.univ)
    (c : ℝ) (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2)
    (hscale : c * (C + 1) * Real.exp 1 ≤ 1 / 2) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (c * Real.rpow (H x) (1 / (k : ℝ)))) ∂μ) ≤
      ENNReal.ofReal (2 * (1 + (C * (2 : ℝ) ^ k) ^ 2)) * μ Set.univ := by
  let L : ℝ := 1 + (C * (2 : ℝ) ^ k) ^ 2
  let f := fun (n : ℕ) (x : α) => ENNReal.ofReal
    ((c * Real.rpow (H x) (1 / (k : ℝ))) ^ n / (n.factorial : ℝ))
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hy : Measurable (fun x => c * Real.rpow (H x) (1 / (k : ℝ))) := by
    change Measurable (fun x => c * (H x) ^ (1 / (k : ℝ)))
    exact (hHm.pow_const (1 / (k : ℝ))).const_mul c
  have hf (n : ℕ) : AEMeasurable (f n) μ :=
    ((hy.pow_const n).div_const (n.factorial : ℝ)).ennreal_ofReal.aemeasurable
  have hgeom : (∑' n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) = 2 := by
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    simp_rw [ENNReal.ofReal_pow (show (0 : ℝ) ≤ 1 / 2 by norm_num), hhalf]
    exact ENNReal.tsum_geometric_two
  calc
    _ = ∫⁻ x, ∑' n : ℕ, f n x ∂μ := lintegral_congr (fun x =>
      ofReal_exp_eq_tsum _ (mul_nonneg hc (Real.rpow_nonneg (hH x) _)))
    _ = ∑' n : ℕ, ∫⁻ x, f n x ∂μ := lintegral_tsum hf
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (L * (1 / 2 : ℝ) ^ n) * μ Set.univ :=
      ENNReal.tsum_le_tsum (fun n => exponential_term_bound μ H hH k hk C hC hmom c hc hc2 hscale n)
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul hL]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, hgeom]
      rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
      dsimp only [L]
      norm_num [mul_comm]

universe u

/-- Uniform polynomial moment growth implies exponential integrability.
The positive constants are chosen before the measurable space, measure or input.
The conclusion uses an extended integral and includes the zero-measure case. -/
theorem moments_to_exponential (k : ℕ) (hk : 1 ≤ k) (C : ℝ) (hC : 0 < C) :
    ∃ c B : ℝ, 0 < c ∧ 0 < B ∧
      ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
        (H : α → ℝ), Measurable H → (∀ x, 0 ≤ H x) →
        (∀ q : ℝ, 2 ≤ q →
          (∫⁻ x, (ENNReal.ofReal (H x)) ^ q ∂μ) ≤
            (ENNReal.ofReal (C * q ^ k)) ^ q * μ Set.univ) →
        (∫⁻ x, ENNReal.ofReal
          (Real.exp (c * Real.rpow (H x) (1 / (k : ℝ))) - 1) ∂μ) ≤
          ENNReal.ofReal B * μ Set.univ := by
  let c : ℝ := (1 / 2) / ((C + 1) * Real.exp 1)
  let L : ℝ := 1 + (C * (2 : ℝ) ^ k) ^ 2
  have hden : 0 < (C + 1) * Real.exp 1 := mul_pos (by linarith) (Real.exp_pos _)
  have hden1 : 1 ≤ (C + 1) * Real.exp 1 := by
    calc
      1 = (1 : ℝ) * 1 := by ring
      _ ≤ (C + 1) * Real.exp 1 := mul_le_mul (by linarith)
        (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)) zero_le_one (by linarith)
  have hc : 0 < c := div_pos (by norm_num) hden
  have hc2 : c ≤ 1 / 2 := div_le_self (by norm_num) hden1
  have hscale : c * (C + 1) * Real.exp 1 ≤ 1 / 2 := by
    dsimp only [c]
    rw [mul_assoc, div_mul_cancel₀ _ hden.ne']
  refine ⟨c, 2 * L, hc, by dsimp only [L]; positivity, ?_⟩
  intro α _ μ _ H hHm hH hmom
  have hbound := exponential_integral_bound μ H hHm hH k hk C hC hmom c hc.le hc2 hscale
  exact (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal
    (sub_le_self (Real.exp (c * Real.rpow (H x) (1 / (k : ℝ)))) zero_le_one))).trans hbound

end ReyZygmund.Overlap
