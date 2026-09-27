import ReyZygmund.Overlap.SetCountable
import ReyZygmund.Overlap.AllMoments
import ReyZygmund.Overlap.MomentTailExact

/-! # All real moments and the exact exponential for countable set overlaps

The overlap is the nonnegative series. Its second moment first proves
almost-everywhere finiteness. Only then is its real representative used in the
norm and exponential statements. The shadow may have measure zero.
-/

open MeasureTheory
open scoped ENNReal

namespace ReyZygmund.Overlap

variable {d : ℕ}

theorem set_overlap_ae_finite_of_high_moments
    (G : Set (Set (Fin d → ℝ))) (hG : G.Countable)
    (hm : ∀ I ∈ G, MeasurableSet I) (hshadow : volume (setShadow G) < ∞)
    (k : ℕ) (C : ℝ)
    (hhigh : ∀ q : ℝ, 2 ≤ q →
      (∫⁻ x, (setOverlap G x) ^ q) ≤
        (ENNReal.ofReal (C * (q - 1) ^ k)) ^ q * volume (setShadow G)) :
    ∀ᵐ x ∂volume, setOverlap G x < ∞ := by
  have hint : (∫⁻ x, (setOverlap G x) ^ (2 : ℝ)) < ∞ :=
    (hhigh 2 (le_refl _)).trans_lt
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg
        (by norm_num) ENNReal.ofReal_ne_top) hshadow)
  filter_upwards [ae_lt_top ((measurable_setOverlap G hG hm).pow_const (2 : ℝ))
    hint.ne] with x hx
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 2)).mp hx

theorem set_overlap_all_moments_on_shadow
    (G : Set (Set (Fin d → ℝ))) (hG : G.Countable)
    (hm : ∀ I ∈ G, MeasurableSet I) (hshadow : volume (setShadow G) < ∞)
    (k : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hhigh : ∀ q : ℝ, 2 ≤ q →
      (∫⁻ x, (setOverlap G x) ^ q) ≤
        (ENNReal.ofReal (C * (q - 1) ^ k)) ^ q * volume (setShadow G))
    (q : ℝ) (hq : 1 ≤ q) :
    (∫⁻ x in setShadow G, (ENNReal.ofReal (setOverlap G x).toReal) ^ q) ≤
      (ENNReal.ofReal (C * q ^ k)) ^ q * volume (setShadow G) := by
  let μ := volume.restrict (setShadow G)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hshadow.ne
  have hrestricted (r : ℝ) (hr : 2 ≤ r) :
      (∫⁻ x, (ENNReal.ofReal (setOverlap G x).toReal) ^ r ∂μ) ≤
        (ENNReal.ofReal (C * (r - 1) ^ k)) ^ r * μ Set.univ := by
    have hr0 : 0 ≤ r := (by norm_num : (0 : ℝ) ≤ 2).trans hr
    apply (lintegral_mono' (μ := μ) (ν := volume) Measure.restrict_le_self
      (fun x => ENNReal.rpow_le_rpow ENNReal.ofReal_toReal_le hr0)).trans
    simpa only [μ, Measure.restrict_apply_univ] using hhigh r hr
  simpa only [μ, Measure.restrict_apply_univ] using
    all_moments_of_high_moments μ (fun x => (setOverlap G x).toReal)
      (measurable_setOverlap G hG hm).ennreal_toReal
      (fun _ => ENNReal.toReal_nonneg) k C hC hrestricted q hq

theorem set_overlap_all_moments
    (G : Set (Set (Fin d → ℝ))) (hG : G.Countable)
    (hm : ∀ I ∈ G, MeasurableSet I) (hshadow : volume (setShadow G) < ∞)
    (k : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hhigh : ∀ q : ℝ, 2 ≤ q →
      (∫⁻ x, (setOverlap G x) ^ q) ≤
        (ENNReal.ofReal (C * (q - 1) ^ k)) ^ q * volume (setShadow G))
    (q : ℝ) (hq : 1 ≤ q) :
    (∫⁻ x, (setOverlap G x) ^ q) ≤
      (ENNReal.ofReal (C * q ^ k)) ^ q * volume (setShadow G) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have ha := set_overlap_ae_finite_of_high_moments G hG hm hshadow k C hhigh
  have hsupport : (setShadow G).indicator (fun x => (setOverlap G x) ^ q) =
      (fun x => (setOverlap G x) ^ q) := by
    funext x
    by_cases hx : x ∈ setShadow G
    · exact Set.indicator_of_mem hx _
    · rw [Set.indicator_of_notMem hx, setOverlap_eq_zero_of_not_mem G x hx,
        ENNReal.zero_rpow_of_pos hq0]
  calc
    _ = ∫⁻ x in setShadow G, (setOverlap G x) ^ q := by
      rw [← lintegral_indicator (measurableSet_setShadow G hG hm), hsupport]
    _ = ∫⁻ x in setShadow G, (ENNReal.ofReal (setOverlap G x).toReal) ^ q := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae ha] with x hx
      rw [ENNReal.ofReal_toReal hx.ne]
    _ ≤ _ := set_overlap_all_moments_on_shadow G hG hm hshadow k C hC hhigh q hq

theorem set_overlap_eLpNorm_of_high_moments
    (G : Set (Set (Fin d → ℝ))) (hG : G.Countable)
    (hm : ∀ I ∈ G, MeasurableSet I) (hshadow : volume (setShadow G) < ∞)
    (k : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hhigh : ∀ q : ℝ, 2 ≤ q →
      (∫⁻ x, (setOverlap G x) ^ q) ≤
        (ENNReal.ofReal (C * (q - 1) ^ k)) ^ q * volume (setShadow G))
    (q : ℝ) (hq : 1 ≤ q) :
    eLpNorm (fun x => (setOverlap G x).toReal) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (C * q ^ k) * (volume (setShadow G)) ^ (1 / q) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have ha := set_overlap_ae_finite_of_high_moments G hG hm hshadow k C hhigh
  have heq : (∫⁻ x, ‖(setOverlap G x).toReal‖ₑ ^ q) =
      ∫⁻ x, (setOverlap G x) ^ q := by
    apply lintegral_congr_ae
    filter_upwards [ha] with x hx
    rw [Real.enorm_toReal hx.ne]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_ne_zero_iff.mpr hq0) ENNReal.ofReal_ne_top
      (measurable_setOverlap G hG hm).ennreal_toReal.aestronglyMeasurable,
    ENNReal.toReal_ofReal hq0.le, heq]
  have h := ENNReal.rpow_le_rpow
    (set_overlap_all_moments G hG hm hshadow k C hC hhigh q hq)
    (one_div_nonneg.mpr hq0.le)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hq0.le),
    ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one] at h
  exact h

/-- The full exponential estimate with factor three. Here `k` is the moment-growth
order, one greater than the endpoint logarithmic order in the application.
-/
theorem set_overlap_exponential_of_high_moments
    (G : Set (Set (Fin d → ℝ))) (hG : G.Countable)
    (hm : ∀ I ∈ G, MeasurableSet I) (hshadow : volume (setShadow G) < ∞)
    (k : ℕ) (hk : 1 ≤ k) (C : ℝ) (hC : 0 < C)
    (hhigh : ∀ q : ℝ, 2 ≤ q →
      (∫⁻ x, (setOverlap G x) ^ q) ≤
        (ENNReal.ofReal (C * (q - 1) ^ k)) ^ q * volume (setShadow G)) :
    (∀ᵐ x ∂volume, setOverlap G x < ∞) ∧
      (∫⁻ x in setShadow G, ENNReal.ofReal
        (Real.exp ((1 / 2 : ℝ) * ((setOverlap G x).toReal / (Real.exp 1 * C)) ^
          (1 / (k : ℝ))))) ≤ 3 * volume (setShadow G) := by
  refine ⟨set_overlap_ae_finite_of_high_moments G hG hm hshadow k C hhigh, ?_⟩
  let μ := volume.restrict (setShadow G)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hshadow.ne
  have hmom (q : ℝ) (hq : 1 ≤ q) :
      (∫⁻ x, ENNReal.ofReal ((setOverlap G x).toReal ^ q) ∂μ) ≤
        ENNReal.ofReal ((C * q ^ k) ^ q) * μ Set.univ := by
    have hq0 : 0 ≤ q := zero_le_one.trans hq
    simpa only [μ, Measure.restrict_apply_univ,
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq0,
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC.le (pow_nonneg hq0 _)) hq0] using
      set_overlap_all_moments_on_shadow G hG hm hshadow k C hC.le hhigh q hq
  simpa only [μ, Measure.restrict_apply_univ] using
    all_polynomial_moments_exponential μ (fun x => (setOverlap G x).toReal)
      (measurable_setOverlap G hG hm).ennreal_toReal
      (fun _ => ENNReal.toReal_nonneg) k hk C hC hmom

end ReyZygmund.Overlap
