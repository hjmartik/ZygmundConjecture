import ReyZygmund.Maximal.WeakerGrid
import ReyZygmund.Maximal.Euclidean
import ReyZygmund.Maximal.Countable
import ReyZygmund.Geometry.ProductContainment
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # The weaker-containment estimate on the whole grid

The finite estimates are uniform in the top rectangles and smallest scales used
for localization. Countable monotone convergence gives the extended power-integral
bound. Almost-everywhere finiteness then permits real-valued representatives and
Lp norms.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- The countable supremum satisfies the uniform power-integral
estimate, with no finite-family or bounded-input restriction. -/
theorem weaker_grid_family_maximal_lintegral
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (hweak : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → ∃ i, R i = S i)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    (∫⁻ x, (familyMaximal G f x) ^ p) ≤
      (ENNReal.ofReal ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1))) ^ p *
          ∫⁻ x, (ENNReal.ofReal |f x|) ^ p := by
  have hc : G.Countable := (countable_gridRectangles D).mono hG
  apply lintegral_familyMaximal_rpow_le G hc f p (zero_lt_one.trans hp)
  intro H
  have hHG : ∀ Q ∈ H.image Subtype.val, Q ∈ G := by
    intro Q hQ
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hQ
    exact R.property
  exact finite_weaker_grid_maximal_lintegral hm hd D (H.image Subtype.val)
    (fun Q hQ => hG (hHG Q hQ))
    (fun R hR S hS => hweak R (hHG R hR) S (hHG S hS)) f p hp hf

/-- The global supremum is finite almost everywhere. This is established
before taking a real representative; divergent suprema are not set to zero
and then silently treated as the maximal function. -/
theorem weaker_grid_family_maximal_ae_finite
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (hweak : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → ∃ i, R i = S i)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∀ᵐ x ∂volume, familyMaximal G f x < ∞ := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hin : (∫⁻ x, (ENNReal.ofReal |f x|) ^ p) < ∞ := by
    simpa only [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal hp0.le] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top hf.eLpNorm_lt_top
  have hout : (∫⁻ x, (familyMaximal G f x) ^ p) < ∞ :=
    lt_of_le_of_lt (weaker_grid_family_maximal_lintegral hm hd D G hG hweak f p hp hf)
      (ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg hp0.le ENNReal.ofReal_ne_top) hin)
  have hc : G.Countable := (countable_gridRectangles D).mono hG
  have ha := ae_lt_top ((measurable_familyMaximal G hc f).pow_const p) hout.ne
  filter_upwards [ha] with x hx
  exact (ENNReal.rpow_lt_top_iff_of_pos hp0).mp hx

/-- Ordinary Lp form for the almost-everywhere finite representative, with
the exact `(p')^(m-1)` factor outside the norm. -/
theorem weaker_grid_family_maximal_eLpNorm
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (hweak : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → ∃ i, R i = S i)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (fun x => (familyMaximal G f x).toReal) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1)) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpE := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hc : G.Countable := (countable_gridRectangles D).mono hG
  have hmM : AEStronglyMeasurable (fun x => (familyMaximal G f x).toReal) volume :=
    (measurable_familyMaximal G hc f).ennreal_toReal.aestronglyMeasurable
  have hfinite := weaker_grid_family_maximal_ae_finite hm hd D G hG hweak f p hp hf
  have heq : (∫⁻ x, ‖(familyMaximal G f x).toReal‖ₑ ^ p) =
      ∫⁻ x, (familyMaximal G f x) ^ p := by
    apply lintegral_congr_ae
    filter_upwards [hfinite] with x hx
    rw [Real.enorm_toReal hx.ne]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpE ENNReal.ofReal_ne_top hmM,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hpE ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le, heq]
  simp_rw [Real.enorm_eq_ofReal_abs]
  have h := ENNReal.rpow_le_rpow
    (weaker_grid_family_maximal_lintegral hm hd D G hG hweak f p hp hf)
      (one_div_nonneg.mpr hp0.le)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp0.le),
    ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] at h
  exact h

/-- The paper's weaker-containment premise uses product-set inclusion
and equality of one coordinate cube. -/
theorem weaker_containment_grid_maximal_eLpNorm
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (hweak : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (fun x => (familyMaximal G f x).toReal) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1)) * eLpNorm f (ENNReal.ofReal p) volume := by
  exact weaker_grid_family_maximal_eLpNorm hm hd D G hG
    (fun R hR S hS hRS => hweak R hR S hS ((productBox_subset_iff R S).mpr hRS))
      f p hp hf

/-- Almost-everywhere finiteness of the Euclidean supremum. -/
theorem euclidean_weaker_grid_maximal_ae_finite
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (hweak : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i)
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∀ᵐ x ∂volume, euclideanFamilyMaximal G f x < ∞ := by
  have hfin := weaker_grid_family_maximal_ae_finite hm hd D G hG
    (fun R hR S hS hRS => hweak R hR S hS ((productBox_subset_iff R S).mpr hRS))
      (fun y => f (flattenCoordinates d y)) p hp (memLp_comp_flattenCoordinates f _ hf)
  have hmap := (volume_preserving_flattenCoordinates d).map_eq
  rw [← hmap]
  apply (ae_map_iff (flattenCoordinates d).measurable.aemeasurable
    ((measurable_euclideanFamilyMaximal G ((countable_gridRectangles D).mono hG) f)
      measurableSet_Iio)).mpr
  simpa only [euclideanFamilyMaximal_flatten, Set.mem_Iio] using hfin

/-- The main norm estimate in ordinary Euclidean coordinates, with the same
dimension-only constant and no finite-family or bounded-input restriction. -/
theorem euclidean_weaker_grid_maximal_eLpNorm
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (hweak : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i)
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (fun x => (euclideanFamilyMaximal G f x).toReal) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1)) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hmeas := (measurable_euclideanFamilyMaximal G
    ((countable_gridRectangles D).mono hG) f).ennreal_toReal
  rw [← eLpNorm_comp_flattenCoordinates _ _ hmeas.aestronglyMeasurable]
  simp_rw [euclideanFamilyMaximal_flatten]
  exact (weaker_containment_grid_maximal_eLpNorm hm hd D G hG hweak
    (fun y => f (flattenCoordinates d y)) p hp (memLp_comp_flattenCoordinates f _ hf)).trans_eq
      (congrArg (ENNReal.ofReal ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1)) * ·)
        (eLpNorm_comp_flattenCoordinates f _ hf.aestronglyMeasurable))

end ReyZygmund
