import ReyZygmund.Definitions.Scalar
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # The quantitative scalar remainder inequality

After the second-derivative calculation, subtract the quadratic term and apply the
supporting-line inequality. This proves the same remainder estimate without the
paper's two successive integrations.

-/

namespace ReyZygmund

open Set

private lemma scalar_segment_pos {b η s : ℝ} (hb : 0 < b) (hbη : 0 < b + η)
    (hs : s ∈ Icc (0 : ℝ) 1) : 0 < b + s * η := by
  by_cases hs1 : s = 1
  · simpa [hs1] using hbη
  have hslt : s < 1 := lt_of_le_of_ne hs.2 hs1
  have hleft := mul_pos (sub_pos.mpr hslt) hb
  have hright := mul_nonneg hs.1 hbη.le
  nlinarith

private lemma scalar_segment_le_max {b η s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    b + s * η ≤ max b (b + η) := by
  calc
    b + s * η = (1 - s) * b + s * (b + η) := by ring
    _ ≤ (1 - s) * max b (b + η) + s * max b (b + η) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr hs.2))
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hs.1)
    _ = max b (b + η) := by ring

/-- A constant second-derivative lower bound gives the normalized remainder. -/
private lemma scalar_remainder_of_second_derivative
    {f f' f'' : ℝ → ℝ} {C : ℝ}
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' s) s)
    (hf' : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt f' (f'' s) s)
    (hlower : ∀ s ∈ Icc (0 : ℝ) 1, 2 * C ≤ f'' s) :
    C ≤ f 1 - f 0 - f' 0 := by
  let F : ℝ → ℝ := fun s => f s - C * s ^ 2
  have hF : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt F (f' s - 2 * C * s) s := by
    intro s hs
    convert (hf s hs).sub (((hasDerivAt_id s).pow 2).const_mul C) using 1
    · rfl
    · dsimp
      ring
  have hF' : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t => f' t - 2 * C * t) (f'' s - 2 * C) s := by
    intro s hs
    convert (hf' s hs).sub ((hasDerivAt_id s).const_mul (2 * C)) using 1
    · rfl
    · ring
  have hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) F :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
      (fun s hs => (hF s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hF s (interior_subset hs)).hasDerivWithinAt)
      (fun s hs => (hF' s (interior_subset hs)).hasDerivWithinAt)
      (fun s hs => sub_nonneg.mpr (hlower s (interior_subset hs)))
  have hslope := hconv.le_slope_of_hasDerivAt
    (show (0 : ℝ) ∈ Icc 0 1 by simp)
    (show (1 : ℝ) ∈ Icc 0 1 by simp)
    (show (0 : ℝ) < 1 by norm_num)
    (hF 0 (by simp))
  simp only [F, slope_def_field, sub_zero, one_pow, mul_one, zero_pow (by decide : 2 ≠ 0),
    mul_zero, div_one] at hslope
  linarith

private noncomputable def scalarPath (r a h b η s : ℝ) : ℝ :=
  (a + s * h) ^ 2 * (b + s * η) ^ (-r)

private noncomputable def scalarPathDeriv (r a h b η s : ℝ) : ℝ :=
  2 * (a + s * h) * h * (b + s * η) ^ (-r) -
    r * (a + s * h) ^ 2 * η * (b + s * η) ^ (-r - 1)

private noncomputable def scalarPathDeriv2 (r a h b η s : ℝ) : ℝ :=
  2 * h ^ 2 * (b + s * η) ^ (-r) -
    4 * r * (a + s * h) * h * η * (b + s * η) ^ (-r - 1) +
    r * (r + 1) * (a + s * h) ^ 2 * η ^ 2 * (b + s * η) ^ (-r - 2)

private lemma scalarPath_hasDerivAt (r a h b η s : ℝ) (hbs : 0 < b + s * η) :
    HasDerivAt (scalarPath r a h b η) (scalarPathDeriv r a h b η s) s := by
  have ha : HasDerivAt (fun t : ℝ => a + t * h) h s := by
    simpa using ((hasDerivAt_id s).mul_const h).const_add a
  have hb : HasDerivAt (fun t : ℝ => b + t * η) η s := by
    simpa using ((hasDerivAt_id s).mul_const η).const_add b
  have hp : HasDerivAt (fun t : ℝ => (b + t * η) ^ (-r))
      (η * (-r) * (b + s * η) ^ (-r - 1)) s :=
    hb.rpow_const (Or.inl (ne_of_gt hbs))
  convert (ha.pow 2).mul hp using 1
  · rfl
  · dsimp [scalarPathDeriv]
    ring

private lemma scalarPathDeriv_hasDerivAt (r a h b η s : ℝ)
    (hbs : 0 < b + s * η) :
    HasDerivAt (scalarPathDeriv r a h b η) (scalarPathDeriv2 r a h b η s) s := by
  have ha : HasDerivAt (fun t : ℝ => a + t * h) h s := by
    simpa using ((hasDerivAt_id s).mul_const h).const_add a
  have hb : HasDerivAt (fun t : ℝ => b + t * η) η s := by
    simpa using ((hasDerivAt_id s).mul_const η).const_add b
  have hp : HasDerivAt (fun t : ℝ => (b + t * η) ^ (-r))
      (η * (-r) * (b + s * η) ^ (-r - 1)) s :=
    hb.rpow_const (Or.inl (ne_of_gt hbs))
  have hp' : HasDerivAt (fun t : ℝ => (b + t * η) ^ (-r - 1))
      (η * (-r - 1) * (b + s * η) ^ (-r - 2)) s := by
    simpa only [show -r - 1 - 1 = -r - 2 by ring] using
      hb.rpow_const (p := -r - 1) (Or.inl (ne_of_gt hbs))
  have hfirst := ((ha.const_mul 2).mul_const h).mul hp
  have hsecond := (((ha.pow 2).const_mul r).mul_const η).mul hp'
  convert hfirst.sub hsecond using 1
  · rfl
  · dsimp [scalarPathDeriv2]
    ring

/-- The completed square and the endpoint bound on the positive denominator. -/
private lemma scalar_second_derivative_bound
    (r x h y η B : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hy : 0 < y) (hyB : y ≤ B) :
    2 * ((1 - r) / (r + 1) * B ^ (-r) * h ^ 2) ≤
      2 * h ^ 2 * y ^ (-r) - 4 * r * x * h * η * y ^ (-r - 1) +
        r * (r + 1) * x ^ 2 * η ^ 2 * y ^ (-r - 2) := by
  have hrpos : 0 < r + 1 := by linarith
  have hy1 : y ^ (-r - 1) = y ^ (-r - 2) * y := by
    calc
      y ^ (-r - 1) = y ^ ((-r - 2) + 1) := by congr 1; ring
      _ = y ^ (-r - 2) * y := Real.rpow_add_one (ne_of_gt hy) _
  have hy0 : y ^ (-r) = y ^ (-r - 2) * y ^ 2 := by
    calc
      y ^ (-r) = y ^ ((-r - 1) + 1) := by congr 1; ring
      _ = y ^ (-r - 1) * y := Real.rpow_add_one (ne_of_gt hy) _
      _ = y ^ (-r - 2) * y ^ 2 := by rw [hy1]; ring
  have hcomplete :
      2 * h ^ 2 * y ^ (-r) - 4 * r * x * h * η * y ^ (-r - 1) +
          r * (r + 1) * x ^ 2 * η ^ 2 * y ^ (-r - 2) =
        r * (r + 1) * y ^ (-r - 2) * (x * η - 2 * y * h / (r + 1)) ^ 2 +
          2 * (1 - r) / (r + 1) * y ^ (-r) * h ^ 2 := by
    rw [hy0, hy1]
    field_simp [ne_of_gt hrpos]
    ring
  have hterm :
      0 ≤ r * (r + 1) * y ^ (-r - 2) * (x * η - 2 * y * h / (r + 1)) ^ 2 :=
    mul_nonneg
      (mul_nonneg (mul_nonneg hr0 hrpos.le) (Real.rpow_nonneg hy.le _))
      (sq_nonneg _)
  have hcoeff : 0 ≤ 2 * (1 - r) / (r + 1) :=
    div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hr1.le)) hrpos.le
  have hpow := Real.rpow_le_rpow_of_nonpos hy hyB (neg_nonpos.mpr hr0)
  calc
    2 * ((1 - r) / (r + 1) * B ^ (-r) * h ^ 2) =
        (2 * (1 - r) / (r + 1) * B ^ (-r)) * h ^ 2 := by ring
    _ ≤ (2 * (1 - r) / (r + 1) * y ^ (-r)) * h ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hcoeff) (sq_nonneg h)
    _ ≤ 2 * h ^ 2 * y ^ (-r) - 4 * r * x * h * η * y ^ (-r - 1) +
        r * (r + 1) * x ^ 2 * η ^ 2 * y ^ (-r - 2) := by
      rw [hcomplete]
      linarith

/-- `lem:scalar-estimate`: the exact remainder for arbitrary signed increments.
The only positivity assumptions concern the two denominator endpoints. -/
theorem scalar_estimate
    (p a h b η : ℝ) (hp : 1 < p) (hp2 : p ≤ 2)
    (hb : 0 < b) (hbη : 0 < b + η) :
    (p - 1) / (3 - p) *
        (h ^ (2 : ℕ) / Real.rpow (max b (b + η)) (2 - p)) ≤
      scalarPsi p (a + h) (b + η) - scalarPsi p a b -
        2 * a * h / Real.rpow b (2 - p) +
        (2 - p) * a ^ (2 : ℕ) * η / Real.rpow b (3 - p) := by
  let r : ℝ := 2 - p
  let B : ℝ := max b (b + η)
  let C : ℝ := (1 - r) / (r + 1) * B ^ (-r) * h ^ 2
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hBpos : 0 < B := lt_of_lt_of_le hb (le_max_left _ _)
  have hrem := scalar_remainder_of_second_derivative
    (f := scalarPath r a h b η) (f' := scalarPathDeriv r a h b η)
    (f'' := scalarPathDeriv2 r a h b η) (C := C)
    (fun s hs => scalarPath_hasDerivAt r a h b η s (scalar_segment_pos hb hbη hs))
    (fun s hs => scalarPathDeriv_hasDerivAt r a h b η s (scalar_segment_pos hb hbη hs))
    (fun s hs => scalar_second_derivative_bound r (a + s * h) h (b + s * η) η B
      hr0 hr1 (scalar_segment_pos hb hbη hs) (scalar_segment_le_max hs))
  have hq0 : scalarPath r a h b η 0 = scalarPsi p a b := by
    simp only [scalarPath, zero_mul, add_zero, scalarPsi, div_eq_mul_inv]
    rw [Real.rpow_neg hb.le]
    rfl
  have hq1 : scalarPath r a h b η 1 = scalarPsi p (a + h) (b + η) := by
    simp only [scalarPath, one_mul, scalarPsi, div_eq_mul_inv]
    rw [Real.rpow_neg hbη.le]
    rfl
  have hC : C = (p - 1) / (3 - p) *
      (h ^ 2 / Real.rpow (max b (b + η)) (2 - p)) := by
    change (1 - r) / (r + 1) * B ^ (-r) * h ^ 2 = _
    have hnum : 1 - r = p - 1 := by dsimp [r]; ring
    have hden : r + 1 = 3 - p := by dsimp [r]; ring
    rw [Real.rpow_neg hBpos.le, hnum, hden]
    dsimp [r, B]
    ring
  have hd0 : scalarPathDeriv r a h b η 0 =
      2 * a * h / Real.rpow b (2 - p) -
        (2 - p) * a ^ 2 * η / Real.rpow b (3 - p) := by
    simp only [scalarPathDeriv, zero_mul, add_zero]
    have hexp : -r - 1 = -(3 - p) := by dsimp [r]; ring
    rw [hexp, Real.rpow_neg hb.le r, Real.rpow_neg hb.le (3 - p)]
    dsimp [r]
    ring
  rw [hC, hq1, hq0, hd0] at hrem
  linarith

end ReyZygmund
