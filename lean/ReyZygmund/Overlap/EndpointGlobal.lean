import ReyZygmund.Overlap.Countable
import ReyZygmund.Overlap.MomentTailExponential

/-! # Countable overlap limits and the endpoint tail argument

The hypotheses are finite overlap estimates on every finite subfamily.
The extended overlap is used for the limit. Its almost-everywhere finiteness
is proved before stating the exponential conclusion for its real representative.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Overlap

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

theorem countable_overlap_lintegral_of_finite
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G.Countable)
    (k : ℕ) (C : ℝ)
    (hfinite : ∀ (H : Finset G) (q : ℝ), 2 ≤ q →
      (∫⁻ x, (ENNReal.ofReal (finiteOverlap (H.image Subtype.val) x)) ^ q) ≤
        (ENNReal.ofReal (C * q ^ k)) ^ q *
          volume (finiteShadow (H.image Subtype.val)))
    (q : ℝ) (hq : 2 ≤ q) :
    (∫⁻ x, (overlap G x) ^ q) ≤
      (ENNReal.ofReal (C * q ^ k)) ^ q * volume (shadow G) := by
  rw [lintegral_overlap_rpow_eq_iSup G hG q
    (lt_of_lt_of_le (by norm_num) hq)]
  apply iSup_le
  intro H
  exact (hfinite H q hq).trans
    (mul_le_mul_right (measure_mono (finiteShadow_subset_shadow G H)) _)

/-- Quantitative moments give both AE finiteness and exponential
integrability on the finite shadow, through the tail and layer-cake proof. -/
theorem countable_overlap_exponential_of_moments
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G.Countable)
    (hshadow : volume (shadow G) < ∞)
    (k : ℕ) (hk : 1 ≤ k) (C : ℝ) (hC : 0 < C)
    (hmom : ∀ q : ℝ, 2 ≤ q →
      (∫⁻ x, (overlap G x) ^ q) ≤
        (ENNReal.ofReal (C * q ^ k)) ^ q * volume (shadow G)) :
    (∀ᵐ x ∂volume, overlap G x < ∞) ∧
      (∫⁻ x in shadow G, ENNReal.ofReal
        (Real.exp (((overlap G x).toReal / (Real.exp 2 * C)) ^
          (1 / (k : ℝ))) - 1)) ≤
        ENNReal.ofReal (Real.exp 4) * volume (shadow G) := by
  have hfinite : (∫⁻ x, (overlap G x) ^ (2 : ℝ)) < ∞ :=
    (hmom 2 (le_refl _)).trans_lt
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg
        (by norm_num) ENNReal.ofReal_ne_top) hshadow)
  have ha := ae_lt_top ((measurable_overlap G hG).pow_const (2 : ℝ)) hfinite.ne
  refine ⟨?_, ?_⟩
  · filter_upwards [ha] with x hx
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 2)).mp hx
  · let μ := volume.restrict (shadow G)
    let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hshadow.ne
    have hm : Measurable (fun x => (overlap G x).toReal) :=
      (measurable_overlap G hG).ennreal_toReal
    have hrestricted (q : ℝ) (hq : 2 ≤ q) :
        (∫⁻ x, ENNReal.ofReal ((overlap G x).toReal ^ q) ∂μ) ≤
          ENNReal.ofReal ((C * q ^ k) ^ q) * μ Set.univ := by
      have hq0 : 0 ≤ q := (by norm_num : (0 : ℝ) ≤ 2).trans hq
      calc
        _ ≤ ∫⁻ x, (overlap G x) ^ q := by
          apply lintegral_mono' Measure.restrict_le_self
          intro x
          calc
            ENNReal.ofReal ((overlap G x).toReal ^ q) =
                (ENNReal.ofReal (overlap G x).toReal) ^ q :=
              (ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq0).symm
            _ ≤ (overlap G x) ^ q :=
              ENNReal.rpow_le_rpow ENNReal.ofReal_toReal_le hq0
        _ ≤ _ := by
          simpa only [μ, Measure.restrict_apply_univ,
            ENNReal.ofReal_rpow_of_nonneg
              (mul_nonneg hC.le (pow_nonneg hq0 k)) hq0] using hmom q hq
    simpa only [μ, Measure.restrict_apply_univ] using
      polynomial_moments_exponential μ (fun x => (overlap G x).toReal)
        hm (fun _ => ENNReal.toReal_nonneg) k hk C hC hrestricted

end ReyZygmund.Overlap
