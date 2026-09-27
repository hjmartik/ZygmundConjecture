import ReyZygmund.Maximal.FamilyProperties

/-! # The upper exponent range on a finite top rectangle

For real `p ≥ 3/2`, the ordinary finite-family norm estimate costs at most `3 * (p
/ (p - 1))^(m - 1)`. The input may be signed and the family need not be
incomparable. All integrals are over the top rectangle.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- The ordinary estimate gives the upper exponent range, with a coefficient uniform
in the top rectangle, smallest scales and family. -/
theorem finite_family_maximal_norm_upper
    (hm : 1 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hd : ∀ i, 0 < d i)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (p : ℝ) (hp : (3 : ℝ) / 2 ≤ p) :
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal G F x) p) (1 / p) ≤
      3 * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow |F.1 x| p) (1 / p) := by
  let c := p / (p - 1)
  let L := ∫ x in productBox I, Real.rpow (finiteFamilyMaximal G F x) p
  let Y := ∫ x in productBox I, Real.rpow |F.1 x| p
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := zero_lt_one.trans hp1
  have hc0 : 0 ≤ c := div_nonneg hp0.le (sub_pos.mpr hp1).le
  have hc3 : c ≤ 3 := by
    apply (div_le_iff₀ (sub_pos.mpr hp1)).mpr
    linarith
  have hL0 : 0 ≤ L := integral_nonneg (fun x =>
    Real.rpow_nonneg (finiteFamilyMaximal_nonneg G F x) p)
  have hY0 : 0 ≤ Y :=
    integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg (F.1 x)) p)
  have hbound := finite_family_maximal_integral I N G hG hd F hf hs p hp1
  change L ≤ Real.rpow c (p * (m : ℝ)) * Y at hbound
  have hexp : (p * (m : ℝ)) * (1 / p) = (m : ℝ) := by
    calc
      _ = (p * (m : ℝ)) / p := by ring
      _ = _ := mul_div_cancel_left₀ _ hp0.ne'
  have hcoeff : c ^ m ≤ 3 * c ^ (m - 1) := by
    calc
      c ^ m = c ^ ((m - 1) + 1) :=
        congrArg (fun k : ℕ => c ^ k) (by omega)
      _ = c ^ (m - 1) * c := pow_succ _ _
      _ ≤ c ^ (m - 1) * 3 :=
        mul_le_mul_of_nonneg_left hc3 (pow_nonneg hc0 _)
      _ = 3 * c ^ (m - 1) := mul_comm _ _
  change Real.rpow L (1 / p) ≤ 3 * c ^ (m - 1) * Real.rpow Y (1 / p)
  calc
    _ ≤ Real.rpow (Real.rpow c (p * (m : ℝ)) * Y) (1 / p) :=
      Real.rpow_le_rpow hL0 hbound (one_div_nonneg.mpr hp0.le)
    _ = c ^ m * Real.rpow Y (1 / p) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.mul_rpow (Real.rpow_nonneg hc0 _) hY0,
        ← Real.rpow_mul hc0, hexp, Real.rpow_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hY0 _)

end ReyZygmund
