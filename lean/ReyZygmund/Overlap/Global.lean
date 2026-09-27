import ReyZygmund.Overlap.Countable
import ReyZygmund.Overlap.FiniteBounds

/-! # Sparse overlap moments on countable grid families

Pass from finite subfamilies to the extended overlap. Finite shadow measure then
gives almost-everywhere finiteness, permitting the real-valued representative. The
disjoint sparse subsets and geometric conditions restrict to every subfamily.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Overlap

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

theorem weaker_sparse_overlap_lintegral
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (hweak : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i)
    (eta : ℝ) (heta : 0 < eta)
    (E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ))
    (hEmeas : ∀ R ∈ G, MeasurableSet (E R))
    (hEsub : ∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)))
    (hEdis : Set.Pairwise G (fun R S => Disjoint (E R) (E S)))
    (hEmass : ∀ R ∈ G, ENNReal.ofReal eta *
      volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤ volume (E R))
    (q : ℝ) (hq : 2 ≤ q) :
    (∫⁻ x, (overlap G x) ^ q) ≤
      (ENNReal.ofReal ((maximalDimensionConstant d + 3) * eta⁻¹ * q ^ (m - 1))) ^ q *
        volume (shadow G) := by
  have hc : G.Countable := (countable_gridRectangles D).mono hG
  rw [lintegral_overlap_rpow_eq_iSup G hc q (lt_of_lt_of_le (by norm_num) hq)]
  apply iSup_le
  intro H
  have hHG : ∀ R ∈ H.image Subtype.val, R ∈ G := by
    intro R hR
    obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp hR
    exact S.2
  have hf := finite_weaker_sparse_overlap_lintegral hm hd D (H.image Subtype.val)
    (fun R hR => hG (hHG R hR))
    (fun R hR S hS => hweak R (hHG R hR) S (hHG S hS)) eta heta E
    (fun R hR => hEmeas R (hHG R hR))
    (fun R hR => hEsub R (hHG R hR))
    (fun R hR S hS hne => hEdis (hHG R hR) (hHG S hS) hne)
    (fun R hR => hEmass R (hHG R hR)) q hq
  exact hf.trans (mul_le_mul_right (measure_mono (finiteShadow_subset_shadow G H)) _)

theorem weaker_sparse_overlap_ae_finite
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (hweak : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i)
    (eta : ℝ) (heta : 0 < eta)
    (E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ))
    (hEmeas : ∀ R ∈ G, MeasurableSet (E R))
    (hEsub : ∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)))
    (hEdis : Set.Pairwise G (fun R S => Disjoint (E R) (E S)))
    (hEmass : ∀ R ∈ G, ENNReal.ofReal eta *
      volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤ volume (E R))
    (hshadow : volume (shadow G) < ∞) :
    ∀ᵐ x ∂volume, overlap G x < ∞ := by
  have hb := weaker_sparse_overlap_lintegral hm hd D G hG hweak eta heta E
    hEmeas hEsub hEdis hEmass 2 (le_refl _)
  have hfinite : (∫⁻ x, (overlap G x) ^ (2 : ℝ)) < ∞ := hb.trans_lt
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) hshadow)
  have hc : G.Countable := (countable_gridRectangles D).mono hG
  have ha := ae_lt_top ((measurable_overlap G hc).pow_const (2 : ℝ)) hfinite.ne
  filter_upwards [ha] with x hx
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 2)).mp hx

theorem weaker_sparse_overlap_eLpNorm
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (hweak : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i)
    (eta : ℝ) (heta : 0 < eta)
    (E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ))
    (hEmeas : ∀ R ∈ G, MeasurableSet (E R))
    (hEsub : ∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)))
    (hEdis : Set.Pairwise G (fun R S => Disjoint (E R) (E S)))
    (hEmass : ∀ R ∈ G, ENNReal.ofReal eta *
      volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤ volume (E R))
    (hshadow : volume (shadow G) < ∞) (q : ℝ) (hq : 2 ≤ q) :
    eLpNorm (fun x => (overlap G x).toReal) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal ((maximalDimensionConstant d + 3) * eta⁻¹ * q ^ (m - 1)) *
        (volume (shadow G)) ^ (1 / q) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hc : G.Countable := (countable_gridRectangles D).mono hG
  have hmeas : AEStronglyMeasurable (fun x => (overlap G x).toReal) volume :=
    (measurable_overlap G hc).ennreal_toReal.aestronglyMeasurable
  have hfinite := weaker_sparse_overlap_ae_finite hm hd D G hG hweak eta heta E
    hEmeas hEsub hEdis hEmass hshadow
  have heq : (∫⁻ x, ‖(overlap G x).toReal‖ₑ ^ q) = ∫⁻ x, (overlap G x) ^ q := by
    apply lintegral_congr_ae
    filter_upwards [hfinite] with x hx
    rw [Real.enorm_toReal hx.ne]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_ne_zero_iff.mpr hq0) ENNReal.ofReal_ne_top hmeas,
    ENNReal.toReal_ofReal hq0.le, heq]
  have h := ENNReal.rpow_le_rpow
    (weaker_sparse_overlap_lintegral hm hd D G hG hweak eta heta E
      hEmeas hEsub hEdis hEmass q hq) (one_div_nonneg.mpr hq0.le)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hq0.le),
    ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one] at h
  exact h

end ReyZygmund.Overlap
