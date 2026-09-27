import ReyZygmund.Maximal.EndpointTruncation
import Mathlib.MeasureTheory.Integral.Prod

/-! # The truncated weak endpoint inequality

Remove the bounded part of the input before applying the weak logarithmic
estimate. Local integrability justifies the rectangle averages; the logarithmic
expression on the right is integrated as a nonnegative extended-valued function
and need not be integrable.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry

/-- The weak endpoint hypothesis, applied after the halved-level truncation,
leaves only input values above half the level. -/
theorem euclidean_endpoint_truncated_distribution
    {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i))))
    (k : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweak : ∀ g : (Fin (∑ i, d i) → ℝ) → ℝ,
      LocallyIntegrable g volume → ∀ t : ℝ, 0 < t →
      volume {x | ENNReal.ofReal t < euclideanFamilyMaximal G g x} ≤
        ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
          (|g x| / t * (Real.log (Real.exp 1 + |g x| / t)) ^ k))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf : LocallyIntegrable f volume)
    (hm : Measurable f) (hn : ∀ x, 0 ≤ f x) (lam : ℝ) (hlam : 0 < lam) :
    volume {x | ENNReal.ofReal lam < euclideanFamilyMaximal G f x} ≤
      ENNReal.ofReal (2 * A / lam) *
        ∫⁻ x in {x | lam / 2 < f x}, ENNReal.ofReal
          (f x * (Real.log (Real.exp 1 + 2 * f x / lam)) ^ k) := by
  let S := {x | lam / 2 < f x}
  let g := S.indicator f
  have hS : MeasurableSet S := measurableSet_lt measurable_const hm
  have hg : LocallyIntegrable g volume := hf.indicator hS
  have ht : 0 < lam / 2 := by positivity
  have hpoint (x) : ENNReal.ofReal
      (|g x| / (lam / 2) * (Real.log (Real.exp 1 + |g x| / (lam / 2))) ^ k) =
      ENNReal.ofReal (2 / lam) * S.indicator
        (fun y => ENNReal.ofReal
          (f y * (Real.log (Real.exp 1 + 2 * f y / lam)) ^ k)) x := by
    by_cases hx : x ∈ S
    · simp only [g, Set.indicator_of_mem hx, abs_of_nonneg (hn x)]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 / lam)]
      congr 1
      have hratio : f x / (lam / 2) = 2 * f x / lam := by ring
      rw [hratio]
      ring
    · simp only [g, Set.indicator_of_notMem hx, abs_zero, zero_div,
        zero_mul, ENNReal.ofReal_zero, mul_zero]
  calc
    _ ≤ volume {x | ENNReal.ofReal (lam / 2) < euclideanFamilyMaximal G g x} :=
      measure_mono (euclidean_maximal_truncation_levelset G f hf hm hn lam hlam)
    _ ≤ ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
        (|g x| / (lam / 2) * (Real.log (Real.exp 1 + |g x| / (lam / 2))) ^ k) :=
      hweak g hg (lam / 2) ht
    _ = _ := by
      simp_rw [hpoint]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_indicator hS, ← mul_assoc, ← ENNReal.ofReal_mul hA]
      congr 2
      ring

end ReyZygmund
