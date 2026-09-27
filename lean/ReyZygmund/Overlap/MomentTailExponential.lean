import ReyZygmund.Overlap.MomentTail
import ReyZygmund.Overlap.TailIntegration

/-! # Polynomial moment growth through the tail and layer-cake route -/

open MeasureTheory Set
open scoped ENNReal

namespace ReyZygmund.Overlap

/-- The moment, tail and layer-cake route gives an explicit exponential bound.
The measure is finite and the moment hypothesis holds for every real
order at least two. -/
theorem polynomial_moments_exponential
    {X : Type} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (H : X → ℝ) (hm : Measurable H) (hn : ∀ x, 0 ≤ H x)
    (k : ℕ) (hk : 1 ≤ k) (C : ℝ) (hC : 0 < C)
    (hmom : ∀ q : ℝ, 2 ≤ q →
      (∫⁻ x, ENNReal.ofReal (H x ^ q) ∂mu) ≤
        ENNReal.ofReal ((C * q ^ k) ^ q) * mu univ) :
    (∫⁻ x, ENNReal.ofReal
      (Real.exp ((H x / (Real.exp 2 * C)) ^ (1 / (k : ℝ))) - 1) ∂mu) ≤
      ENNReal.ofReal (Real.exp 4) * mu univ := by
  let Y := fun x => (H x / (Real.exp 2 * C)) ^ (1 / (k : ℝ))
  have hden : 0 < Real.exp 2 * C := mul_pos (Real.exp_pos _) hC
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hY : Measurable Y := by dsimp [Y]; fun_prop
  have hY0 : ∀ x, 0 ≤ Y x := fun x => Real.rpow_nonneg (div_nonneg (hn x) hden.le) _
  have hpow (x : X) : Y x ^ k = H x / (Real.exp 2 * C) := by
    dsimp [Y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg (hn x) hden.le),
      one_div_mul_cancel hk0, Real.rpow_one]
  have htail (u : ℝ) (hu : 0 ≤ u) :
      mu {x | u < Y x} ≤ ENNReal.ofReal (Real.exp 4 * Real.exp (-2 * u)) * mu univ := by
    apply le_trans (measure_mono ?_)
      (polynomial_moments_tail mu H hm hn k C hC hmom u hu)
    intro x hx
    change Real.exp 2 * C * u ^ k < H x
    have hh : u ^ k < Y x ^ k := pow_lt_pow_left₀ hx hu (by omega)
    rw [hpow x] at hh
    simpa only [mul_comm (u ^ k) (Real.exp 2 * C)] using (lt_div_iff₀ hden).mp hh
  have h := exponential_tail_lintegral mu Y hY hY0 (Real.exp 4) 2 1
    (Real.exp_nonneg _) (by norm_num) (by norm_num) htail
  simpa only [Y, one_mul, mul_one, show (2 : ℝ) - 1 = 1 by norm_num, div_one] using h

end ReyZygmund.Overlap
