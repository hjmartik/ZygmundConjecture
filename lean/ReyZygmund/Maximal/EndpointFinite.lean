import ReyZygmund.Maximal.EndpointDistribution
import ReyZygmund.Maximal.EndpointStrong
import ReyZygmund.Maximal.FiniteIdentification

/-! # Endpoint interpolation for finite rectangle maxima

The finite supremum is finite at every point, before its real representative
is used. No grid or incomparability assumption enters this analytic step.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund

open Geometry

/-- The finite maximal function has the quantitative strong power
bound furnished by an endpoint estimate. -/
theorem finite_endpoint_maximal_power
    {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i))))
    (k : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweak : ∀ g : (Fin (∑ i, d i) → ℝ) → ℝ,
      LocallyIntegrable g volume → ∀ t : ℝ, 0 < t →
      volume {x | ENNReal.ofReal t < euclideanFamilyMaximal (G : Set _) g x} ≤
        ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
          (|g x| / t * (Real.log (Real.exp 1 + |g x| / t)) ^ k))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf : LocallyIntegrable f volume)
    (hm : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
    (∫⁻ x, ENNReal.ofReal ((euclideanFamilyMaximal (G : Set _) f x).toReal ^ p)) ≤
      ENNReal.ofReal (8 * A * Real.exp 2 * (k.factorial : ℝ) /
        (p - 1) ^ (k + 1)) * ∫⁻ x, ENNReal.ofReal (f x ^ p) := by
  apply endpoint_distribution_strong_power volume f
    (fun x => (euclideanFamilyMaximal (G : Set _) f x).toReal)
    hm hn (measurable_euclideanFamilyMaximal _ G.countable_toSet f).ennreal_toReal
    (fun _ => ENNReal.toReal_nonneg) k p A hp hp2 hA
  intro t ht
  have heq : {x | t < (euclideanFamilyMaximal (G : Set _) f x).toReal} =
      {x | ENNReal.ofReal t < euclideanFamilyMaximal (G : Set _) f x} := by
    ext x
    change (t < (euclideanFamilyMaximal (G : Set _) f x).toReal) ↔
      ENNReal.ofReal t < euclideanFamilyMaximal (G : Set _) f x
    calc
      _ ↔ ENNReal.ofReal t <
          ENNReal.ofReal (euclideanFamilyMaximal (G : Set _) f x).toReal :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).symm
      _ ↔ _ := by rw [ENNReal.ofReal_toReal (euclideanFamilyMaximal_finset_lt_top G f x).ne]
  rw [heq]
  exact euclidean_endpoint_truncated_distribution (G : Set _) k A hA hweak f hf hm hn t ht

/-- A convenient p-th-power form of the paper's bound, with the constant
chosen independently of p. -/
theorem finite_endpoint_maximal_power_uniform
    {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i))))
    (k : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweak : ∀ g : (Fin (∑ i, d i) → ℝ) → ℝ,
      LocallyIntegrable g volume → ∀ t : ℝ, 0 < t →
      volume {x | ENNReal.ofReal t < euclideanFamilyMaximal (G : Set _) g x} ≤
        ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
          (|g x| / t * (Real.log (Real.exp 1 + |g x| / t)) ^ k))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf : LocallyIntegrable f volume)
    (hm : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
    (∫⁻ x, ENNReal.ofReal ((euclideanFamilyMaximal (G : Set _) f x).toReal ^ p)) ≤
      ENNReal.ofReal ((max 1 (8 * A * Real.exp 2 * (k.factorial : ℝ)) /
        (p - 1) ^ (k + 1)) ^ p) * ∫⁻ x, ENNReal.ofReal (f x ^ p) := by
  let D : ℝ := max 1 (8 * A * Real.exp 2 * (k.factorial : ℝ))
  have heps : 0 < p - 1 := by linarith
  have heps1 : p - 1 ≤ 1 := by linarith
  have hden : 0 < (p - 1) ^ (k + 1) := pow_pos heps _
  have hden1 : (p - 1) ^ (k + 1) ≤ 1 := pow_le_one₀ heps.le heps1
  have hD : 1 ≤ D := le_max_left _ _
  have hC : 1 ≤ D / (p - 1) ^ (k + 1) := (le_div_iff₀ hden).mpr (by simpa using hden1.trans hD)
  have hc : 8 * A * Real.exp 2 * (k.factorial : ℝ) / (p - 1) ^ (k + 1) ≤
      (D / (p - 1) ^ (k + 1)) ^ p := by
    calc
      _ ≤ D / (p - 1) ^ (k + 1) :=
        div_le_div_of_nonneg_right (le_max_right _ _) hden.le
      _ = (D / (p - 1) ^ (k + 1)) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hC hp.le
  exact (finite_endpoint_maximal_power G k A hA hweak f hf hm hn p hp hp2).trans
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal hc) _)

end ReyZygmund
