import ReyZygmund.Selection.Exponential
import ReyZygmund.Scalar.OrliczYoung
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # The finite rounded endpoint estimate

Selection, the overlap pairing and the logarithmic Young inequality
give a bound for every finite high-average shadow. The right-hand integral
is extended-valued; no global integrability or finite-Orlicz assumption is
added to the locally integrable input.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Selection

open Geometry Overlap

private theorem finite_lintegral_pairing
    {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i))))
    (a : (Fin (∑ i, d i) → ℝ) → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hameas : AEMeasurable a volume) :
    (∫⁻ x in finiteShadow G, ENNReal.ofReal (a x * finiteOverlap G x)) =
      ∑ R ∈ G, ∫⁻ x in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)),
        ENNReal.ofReal (a x) := by
  have hpoint (x) : ENNReal.ofReal (a x * finiteOverlap G x) =
      ∑ R ∈ G, (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)).indicator
        (fun x => ENNReal.ofReal (a x)) x := by
    rw [finiteOverlap, Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg
      (fun R _ => mul_nonneg (ha x) (Set.indicator_nonneg (fun _ _ => zero_le_one) x))]
    apply Finset.sum_congr rfl
    intro R _
    by_cases hx : x ∈ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) <;> simp [hx]
  have hsupp : (finiteShadow G).indicator
      (fun x => ENNReal.ofReal (a x * finiteOverlap G x)) =
        (fun x => ENNReal.ofReal (a x * finiteOverlap G x)) := by
    funext x
    by_cases hx : x ∈ finiteShadow G
    · simp [hx]
    · simp [hx, finiteOverlap_eq_zero_of_not_mem G x hx]
  rw [← lintegral_indicator (measurableSet_finiteShadow G), hsupp]
  simp_rw [hpoint]
  rw [lintegral_finsetSum' G (fun R _ =>
    hameas.ennreal_ofReal.indicator (flatProductBox R).measurableSet_coe)]
  exact Finset.sum_congr rfl (fun R _ => lintegral_indicator (flatProductBox R).measurableSet_coe _)

private theorem ennreal_absorb_half (x y : ℝ≥0∞) (hx : x ≠ ∞)
    (h : x ≤ y + ENNReal.ofReal (1 / 2 : ℝ) * x) : x ≤ 2 * y := by
  by_cases hy : y = ∞
  · simp [hy]
  have hmul : ENNReal.ofReal (1 / 2 : ℝ) * x ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx
  have hr := (ENNReal.toReal_le_toReal hx (ENNReal.add_ne_top.mpr ⟨hy, hmul⟩)).mpr h
  rw [ENNReal.toReal_add hy hmul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hr
  apply (ENNReal.toReal_le_toReal hx (ENNReal.mul_ne_top (by norm_num) hy)).mp
  rw [ENNReal.toReal_mul]
  norm_num
  linarith

/-- The finite high-average shadow estimate, with arbitrary signed locally
integrable input and arbitrary positive level. -/
theorem finite_rounded_endpoint_shadow
    (n : ℕ) (d : Fin (n + 1) → ℕ) (hn : 2 ≤ n) (hd : ∀ i, 0 < d i) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D : ∀ i, DyadicGrid (d i))
        (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)), Monotone phi →
      ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
      ∀ (lam : ℝ), 0 < lam → ∀ F : Finset (∀ i, Box (Fin (d i))),
      (↑F : Set (∀ i, Box (Fin (d i)))) ⊆ roundedGridRectangles D phi →
      (∀ R ∈ F, lam <
        (∫ x in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), |f x|) /
          volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) →
      volume (finiteShadow F) ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
        (|f x| / lam * (Real.log (Real.exp 1 + |f x| / lam)) ^ (n - 1)) := by
  obtain ⟨c, B, hc, hB, hexp⟩ := selected_rounded_exponential n d hn hd
  let C1 : ℝ := 4 ^ (n + 2)
  have hC1 : 0 < C1 := by positivity
  obtain ⟨C3, hC3, hyoung⟩ := Scalar.orlicz_young (n - 1) (by omega) c C1 B hc hC1 hB
  refine ⟨2 * C3, mul_pos (by norm_num) hC3, ?_⟩
  intro D phi hphi f hf lam hlam F hF hlevel
  obtain ⟨G, hGF, hshadow, hoverlap⟩ := finite_selection_with_comparable_shadow hd D F
    (hF.trans (roundedGridRectangles_subset D phi))
  have hG : (↑G : Set (∀ i, Box (Fin (d i)))) ⊆ roundedGridRectangles D phi :=
    fun _ hR => hF (hGF hR)
  have hsub : finiteShadow G ⊆ finiteShadow F := by
    intro x hx
    obtain ⟨R, hR, hx⟩ := Set.mem_iUnion₂.mp hx
    exact flatProductBox_subset_finiteShadow F R (hGF hR) hx
  let a := fun x => |f x| / lam
  have ha (x) : 0 ≤ a x := div_nonneg (abs_nonneg _) hlam.le
  have hameas : AEMeasurable a volume := by
    simpa only [a, Real.norm_eq_abs, div_eq_mul_inv] using
      hf.aestronglyMeasurable.norm.aemeasurable.mul_const lam⁻¹
  have hai (R : ∀ i, Box (Fin (d i))) : IntegrableOn a (flatProductBox R) volume := by
    have hi := (hf.integrableOn_isCompact (flatProductBox R).isCompact_Icc).mono_set
      (flatProductBox R).coe_subset_Icc
    exact hi.abs.div_const lam
  have havg (R) (hR : R ∈ G) : volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤
      ∫⁻ x in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), ENNReal.ofReal (a x) := by
    have hv : 0 < volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) := by
      simpa only [Measure.real, volume_flatProductBox] using productBox_volume_pos R
    have hmean := (lt_div_iff₀ hv).mp (hlevel R (hGF hR))
    have hreal : volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤
        ∫ x in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), a x := by
      rw [show (∫ x in (flatProductBox R : Set _), a x) =
        (∫ x in (flatProductBox R : Set _), |f x|) / lam from integral_div lam (fun x => |f x|)]
      exact (le_div_iff₀ hlam).mpr (by simpa only [mul_comm] using hmean.le)
    have hb := ENNReal.ofReal_le_ofReal hreal
    rwa [ofReal_measureReal (flatProductBox R).isBounded.measure_lt_top.ne,
      ofReal_integral_eq_lintegral_ofReal (hai R) (Filter.Eventually.of_forall ha)] at hb
  have hpair : volume (finiteShadow G) ≤
      ∫⁻ x in finiteShadow G, ENNReal.ofReal (a x * finiteOverlap G x) := by
    rw [finite_lintegral_pairing G a ha hameas]
    calc
      _ ≤ ∑ R ∈ G, volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) :=
        measure_biUnion_finset_le G _
      _ ≤ _ := Finset.sum_le_sum havg
  have hshadow' : volume (finiteShadow F) ≤ ENNReal.ofReal C1 * volume (finiteShadow G) := by
    change volume.real (finiteShadow F) ≤ C1 * volume.real (finiteShadow G) at hshadow
    have h := ENNReal.ofReal_le_ofReal hshadow
    simpa only [ofReal_measureReal (volume_finiteShadow_lt_top F).ne,
      ENNReal.ofReal_mul hC1.le, ofReal_measureReal (volume_finiteShadow_lt_top G).ne] using h
  let Y := ∫⁻ x, ENNReal.ofReal (a x * (Real.log (Real.exp 1 + a x)) ^ (n - 1))
  let v := fun x => ENNReal.ofReal
    (Real.exp (c * Real.rpow (finiteOverlap G x) (1 / ((n - 1 : ℕ) : ℝ))))
  have hvmeas : Measurable v := by
    dsimp [v]
    simpa only [Real.rpow_eq_pow] using
      (((measurable_finiteOverlap G).pow_const (1 / ((n - 1 : ℕ) : ℝ))).const_mul c).exp.ennreal_ofReal
  have hyoung' (x) : ENNReal.ofReal C1 * ENNReal.ofReal (a x * finiteOverlap G x) ≤
      ENNReal.ofReal C3 * ENNReal.ofReal (a x * (Real.log (Real.exp 1 + a x)) ^ (n - 1)) +
        ENNReal.ofReal ((2 * B)⁻¹) * v x := by
    have h := (ENNReal.ofReal_le_ofReal (hyoung (a x) (finiteOverlap G x)
      (ha x) (finiteOverlap_nonneg G x))).trans ENNReal.ofReal_add_le
    simpa only [mul_assoc, ENNReal.ofReal_mul hC1.le, ENNReal.ofReal_mul hC3.le,
      ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * B)⁻¹), v] using h
  have hbound : volume (finiteShadow F) ≤
      ENNReal.ofReal C3 * Y + ENNReal.ofReal (1 / 2 : ℝ) * volume (finiteShadow F) := by
    calc
      _ ≤ ENNReal.ofReal C1 * ∫⁻ x in finiteShadow G,
          ENNReal.ofReal (a x * finiteOverlap G x) :=
        hshadow'.trans (mul_le_mul_right hpair _)
      _ = ∫⁻ x in finiteShadow G, ENNReal.ofReal C1 *
          ENNReal.ofReal (a x * finiteOverlap G x) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ x in finiteShadow G,
          ENNReal.ofReal C3 * ENNReal.ofReal (a x * (Real.log (Real.exp 1 + a x)) ^ (n - 1)) +
          ENNReal.ofReal ((2 * B)⁻¹) * v x := lintegral_mono hyoung'
      _ = ENNReal.ofReal C3 * (∫⁻ x in finiteShadow G,
          ENNReal.ofReal (a x * (Real.log (Real.exp 1 + a x)) ^ (n - 1))) +
          ENNReal.ofReal ((2 * B)⁻¹) * ∫⁻ x in finiteShadow G, v x := by
        rw [lintegral_add_right _ (hvmeas.const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal C3 * Y +
          ENNReal.ofReal ((2 * B)⁻¹) * (ENNReal.ofReal B * volume (finiteShadow G)) :=
        add_le_add (mul_le_mul_right (setLIntegral_le_lintegral _ _) _)
          (mul_le_mul_right (hexp D phi hphi G hG hoverlap) _)
      _ = ENNReal.ofReal C3 * Y + ENNReal.ofReal (1 / 2 : ℝ) * volume (finiteShadow G) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * B)⁻¹)]
        congr 3
        field_simp
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_right (measure_mono hsub) _)
  have hfinal := ennreal_absorb_half _ _ (volume_finiteShadow_lt_top F).ne hbound
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    mul_assoc, Y, a] using hfinal

end ReyZygmund.Selection
