import ReyZygmund.Maximal.GlobalSquareFinite
import ReyZygmund.Maximal.SignedGlobalLimit

/-! # The square estimate on the whole grid

An almost-everywhere finite difference expansion gives a bounded measurable
representative of the input. Uniform finite averaging estimates and directed
convergence then give the full-grid maximum, including at p = 1. No additional
regularity of the input is assumed.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- The power-integral estimate has one dimensional constant, independent of
the averaging tests, expansion size, grid and exponent in the stated range. -/
theorem signed_grid_square_lintegral
    (D : ∀ i, DyadicGrid (d i)) (hd : ∀ i, 0 < d i)
    (H : Finset (∀ i, Box (Fin (d i)))) (hH : (↑H : Set _) ⊆ gridRectangles D)
    (F : boundedMeasurableFunctions d)
    (hex : F.1 = fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x)
    (p : ℝ) (hp : 1 ≤ p) (hp3 : p ≤ (3 : ℝ) / 2) :
    (∫⁻ x, (signedGridMaximal D F.1 x) ^ p) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (6 * (∑ i, d i) + 10)) *
        ENNReal.ofReal (∫ x, Real.rpow (finiteDifferenceSquare H F.1 x) p) := by
  apply lintegral_signedGridMaximal_rpow_le D F.1 p (zero_lt_one.trans_le hp)
  intro A
  apply finite_signed_grid_square_lintegral D hd H hH F hex (A.image Subtype.val)
    ?_ p hp hp3
  intro Q hQ
  obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hQ
  exact R.2

/-- Full source square estimate and the finiteness facts required for its
ordinary Lp interpretation. The finite expansion is only assumed AE. -/
theorem full_grid_square_estimate
    (D : ∀ i, DyadicGrid (d i)) (hd : ∀ i, 0 < d i)
    (H : Finset (∀ i, Box (Fin (d i)))) (hH : (↑H : Set _) ⊆ gridRectangles D)
    (g : ProductPoint d → ℝ)
    (hex : g =ᵐ[volume] fun x => ∑ Q ∈ H, rawProductDifference Q g x)
    (p : ℝ) (hp : 1 ≤ p) (hp3 : p ≤ (3 : ℝ) / 2) :
    Integrable g volume ∧
      Measurable (signedGridMaximal D g) ∧ Measurable (fullGridSquare D g) ∧
      (∀ᵐ x ∂volume, signedGridMaximal D g x < ∞) ∧
      (∀ᵐ x ∂volume, fullGridSquare D g x < ∞) ∧
      MemLp (fun x => (signedGridMaximal D g x).toReal) (ENNReal.ofReal p) volume ∧
      MemLp (fun x => (fullGridSquare D g x).toReal) (ENNReal.ofReal p) volume ∧
      eLpNorm (fun x => (signedGridMaximal D g x).toReal) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal ((2 : ℝ) ^ (6 * (∑ i, d i) + 10)) *
          eLpNorm (fun x => (fullGridSquare D g x).toReal) (ENNReal.ofReal p) volume := by
  obtain ⟨F, hgf, _, _, hF⟩ := finite_raw_expansion_representative H g hex
  refine ⟨finite_raw_expansion_integrable H g hex,
    measurable_signedGridMaximal D g, measurable_fullGridSquare D g, ?_⟩
  rw [signedGridMaximal_congr_ae D hgf, fullGridSquare_congr_ae D hgf]
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hpE := ENNReal.ofReal_ne_zero_iff.mpr hp0
  let C : ℝ := (2 : ℝ) ^ (6 * (∑ i, d i) + 10)
  have hC : 1 ≤ C := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hCE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal C := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hC
  have hi := integrable_rpow_finiteDifferenceSquare H F.1 p hp0
  have hs (x : ProductPoint d) : fullGridSquare D F.1 x =
      ENNReal.ofReal (finiteDifferenceSquare H F.1 x) :=
    fullGridSquare_eq_ofReal_finiteDifferenceSquare D hd H hH F hF x
  have hsfinite : ∀ᵐ x ∂volume, fullGridSquare D F.1 x < ∞ :=
    Filter.Eventually.of_forall (fun x => by rw [hs x]; exact ENNReal.ofReal_lt_top)
  have hsint : (∫⁻ x, (fullGridSquare D F.1 x) ^ p) =
      ENNReal.ofReal (∫ x, Real.rpow (finiteDifferenceSquare H F.1 x) p) := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal (Real.rpow (finiteDifferenceSquare H F.1 x) p) := by
        apply lintegral_congr
        intro x
        rw [hs x]
        exact ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) hp0.le
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (Real.sqrt_nonneg _) p))).symm
  have hbound := signed_grid_square_lintegral D hd H hH F hF p hp hp3
  have hMfiniteIntegral : (∫⁻ x, (signedGridMaximal D F.1 x) ^ p) < ∞ :=
    lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hMfinite := signedGridMaximal_ae_finite_of_lintegral_lt_top D F.1 p hp0 hMfiniteIntegral
  have hMlp := memLp_signedGridMaximal_toReal_of_lintegral_lt_top D F.1 p hp0 hMfiniteIntegral
  have hSmeas : AEStronglyMeasurable (fun x => (fullGridSquare D F.1 x).toReal) volume :=
    (measurable_fullGridSquare D F.1).ennreal_toReal.aestronglyMeasurable
  have hMnorm : (∫⁻ x, ‖(signedGridMaximal D F.1 x).toReal‖ₑ ^ p) =
      ∫⁻ x, (signedGridMaximal D F.1 x) ^ p := by
    apply lintegral_congr_ae
    filter_upwards [hMfinite] with x hx
    rw [Real.enorm_toReal hx.ne]
  have hSnorm : (∫⁻ x, ‖(fullGridSquare D F.1 x).toReal‖ₑ ^ p) =
      ∫⁻ x, (fullGridSquare D F.1 x) ^ p := by
    apply lintegral_congr_ae
    filter_upwards [hsfinite] with x hx
    rw [Real.enorm_toReal hx.ne]
  have hSlp : MemLp (fun x => (fullGridSquare D F.1 x).toReal) (ENNReal.ofReal p) volume := by
    apply memLp_iff.mpr
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hpE ENNReal.ofReal_ne_top hSmeas).mpr
    rw [ENNReal.toReal_ofReal hp0.le, hSnorm, hsint]
    exact ENNReal.ofReal_lt_top
  refine ⟨hMfinite, hsfinite, hMlp, hSlp, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpE ENNReal.ofReal_ne_top hMlp.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hpE ENNReal.ofReal_ne_top hSmeas,
    ENNReal.toReal_ofReal hp0.le, hMnorm, hSnorm]
  have hpower : (∫⁻ x, (signedGridMaximal D F.1 x) ^ p) ≤
      (ENNReal.ofReal C) ^ p * (∫⁻ x, (fullGridSquare D F.1 x) ^ p) := by
    rw [hsint]
    exact hbound.trans (mul_le_mul_left (ENNReal.le_rpow_self_of_one_le hCE hp) _)
  have h := ENNReal.rpow_le_rpow hpower (one_div_nonneg.mpr hp0.le)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp0.le),
    ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] at h
  exact h

end ReyZygmund
