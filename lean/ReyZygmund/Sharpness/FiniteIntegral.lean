import ReyZygmund.Overlap.FiniteIdentification
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Real integrals of finite overlap exponentials

The overlap is a finite indicator sum. Its bound by the family's cardinality,
together with finite shadow measure, gives integrability of the exponential on the
shadow. This identifies the real and extended integrals in the sharpness
statement.
-/

open BoxIntegral MeasureTheory Filter
open scoped BigOperators Classical ENNReal Topology

namespace ReyZygmund.Sharpness

open Overlap

variable {m : ℕ} {d : Fin m → ℕ}

theorem finite_overlap_exponential_nonneg
    (H : Finset (∀ i, Box (Fin (d i)))) (c beta : ℝ) (hc : 0 ≤ c)
    (x : Fin (∑ i, d i) → ℝ) :
    0 ≤ Real.exp (c * Real.rpow (finiteOverlap H x) beta) - 1 := by
  apply sub_nonneg.mpr
  exact Real.one_le_exp (mul_nonneg hc (Real.rpow_nonneg (finiteOverlap_nonneg H x) beta))

/-- The finite overlap bound is derived from the rectangle indicators. -/
theorem integrableOn_finite_overlap_exponential
    (H : Finset (∀ i, Box (Fin (d i)))) (c beta : ℝ)
    (hc : 0 < c) (hbeta : 0 < beta) :
    IntegrableOn (fun x => Real.exp (c * Real.rpow (finiteOverlap H x) beta) - 1)
      (finiteShadow H) volume := by
  have hmeas : Measurable
      (fun x => Real.exp (c * Real.rpow (finiteOverlap H x) beta) - 1) := by
    simpa only [Real.rpow_eq_pow] using
      (((measurable_finiteOverlap H).pow_const beta).const_mul c).exp.sub_const 1
  apply IntegrableOn.of_bound (volume_finiteShadow_lt_top H)
    hmeas.aestronglyMeasurable (Real.exp (c * Real.rpow (H.card : ℝ) beta))
  apply Eventually.of_forall
  intro x
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (finite_overlap_exponential_nonneg H c beta hc.le x)]
  have hpow : Real.rpow (finiteOverlap H x) beta ≤ Real.rpow (H.card : ℝ) beta :=
    Real.rpow_le_rpow (finiteOverlap_nonneg H x) (finiteOverlap_le_card H x) hbeta.le
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpow hc.le)
  linarith

/-- The extended overlap's real representative is integrable for
finite families, by the proved pointwise finite-sum identification. -/
theorem integrableOn_overlap_finset_exponential
    (H : Finset (∀ i, Box (Fin (d i)))) (c beta : ℝ)
    (hc : 0 < c) (hbeta : 0 < beta) :
    IntegrableOn (fun x => Real.exp (c * Real.rpow
      (overlap (H : Set (∀ i, Box (Fin (d i)))) x).toReal beta) - 1)
      (shadow (H : Set (∀ i, Box (Fin (d i))))) volume := by
  simpa only [shadow_finset, toReal_overlap_finset] using
    integrableOn_finite_overlap_exponential H c beta hc hbeta

/-- The challenge's ENNReal subtraction is exactly the nonnegative real
exponential-minus-one integral, with no default divergent integral. -/
theorem lintegral_overlap_finset_exponential_eq
    (H : Finset (∀ i, Box (Fin (d i)))) (c beta : ℝ)
    (hc : 0 < c) (hbeta : 0 < beta) :
    (∫⁻ x in shadow (H : Set (∀ i, Box (Fin (d i)))), ENNReal.ofReal
      (Real.exp (c * Real.rpow
        (overlap (H : Set (∀ i, Box (Fin (d i)))) x).toReal beta)) - 1) =
      ENNReal.ofReal (∫ x in finiteShadow H,
        Real.exp (c * Real.rpow (finiteOverlap H x) beta) - 1) := by
  rw [shadow_finset]
  simp_rw [toReal_overlap_finset]
  calc
    _ = ∫⁻ x in finiteShadow H, ENNReal.ofReal
        (Real.exp (c * Real.rpow (finiteOverlap H x) beta) - 1) := by
      apply lintegral_congr
      intro x
      rw [ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_one]
    _ = _ := (ofReal_integral_eq_lintegral_ofReal
      (integrableOn_finite_overlap_exponential H c beta hc hbeta)
      (Eventually.of_forall (finite_overlap_exponential_nonneg H c beta hc.le))).symm

/-- The extended-valued formulation of the finite-family sharpness limit
is equivalent to divergence of its real integrals. -/
theorem tendsto_finite_overlap_exponential_iff
    (G : ℕ → Finset (∀ i, Box (Fin (d i)))) (c beta : ℝ)
    (hc : 0 < c) (hbeta : 0 < beta) :
    Tendsto (fun N : ℕ =>
      ∫⁻ x in shadow (G N : Set (∀ i, Box (Fin (d i)))), ENNReal.ofReal
        (Real.exp (c * Real.rpow
          (overlap (G N : Set (∀ i, Box (Fin (d i)))) x).toReal beta)) - 1)
      atTop (𝓝 ∞) ↔
    Tendsto (fun N : ℕ => ∫ x in finiteShadow (G N),
      Real.exp (c * Real.rpow (finiteOverlap (G N) x) beta) - 1) atTop atTop := by
  simp_rw [lintegral_overlap_finset_exponential_eq
    (c := c) (beta := beta) (hc := hc) (hbeta := hbeta)]
  exact ENNReal.tendsto_ofReal_nhds_top

end ReyZygmund.Sharpness
