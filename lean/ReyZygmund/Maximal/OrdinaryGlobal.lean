import ReyZygmund.Maximal.OrdinaryGrid
import ReyZygmund.Maximal.Euclidean

/-! # The ordinary maximal estimate on arbitrary product grids

Sum the finite estimates over disjoint top rectangles, then pass to the countable
supremum. Almost-everywhere finiteness is proved before using real-valued
representatives. The coefficient is `(p / (p - 1)) ^ m` for every real `p > 1`;
incomparability is not required.


-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- The all-real-exponent ordinary estimate for a finite arbitrary-grid
family. Local integrability is derived from the global Lp premise. -/
theorem finite_ordinary_grid_maximal_integral
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : ↑G ⊆ gridRectangles D)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    (∫ x, Real.rpow (finiteFunctionMaximal G f x) p) ≤
      Real.rpow (p / (p - 1)) (p * (m : ℝ)) *
        ∫ x, Real.rpow |f x| p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpE : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have hpow : Integrable (fun x => Real.rpow |f x| p) volume := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le, Real.rpow_eq_pow] using
      hf.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
  have hlocal (R : ∀ i, Box (Fin (d i))) : IntegrableOn f (productBox R) volume := by
    let : IsFiniteMeasure (volume.restrict (productBox R)) :=
      isFiniteMeasure_restrict.mpr (productBox_volume_lt_top R).ne
    exact MemLp.integrable hpE (hf.restrict (productBox R))
  have hC : 0 ≤ Real.rpow (p / (p - 1)) (p * (m : ℝ)) :=
    Real.rpow_nonneg (div_nonneg hp0.le (sub_pos.mpr hp).le) _
  obtain ⟨_k, N, T, _, hdis, hcover, hcut⟩ := exists_finite_grid_roots D G hG
  have hroot (R : ∀ i, Box (Fin (d i))) (hR : R ∈ T) :
      (∫ x in productBox R,
        Real.rpow (finiteFunctionMaximal (G.filter (fun Q => ∀ i, Q i ≤ R i)) f x) p) ≤
      Real.rpow (p / (p - 1)) (p * (m : ℝ)) *
        ∫ x in productBox R, Real.rpow |f x| p :=
    finite_ordinary_general_input_integral R (fun _ => N) hd
      (G.filter (fun Q => ∀ i, Q i ≤ R i)) (hcut R hR) f p hp
      (hlocal R) hpow.integrableOn
  have hsum : (∑ R ∈ T, ∫ x in productBox R, Real.rpow |f x| p) ≤
      ∫ x, Real.rpow |f x| p := by
    rw [← integral_biUnion_finset T (fun R _ => measurableSet_productBox R)
      hdis (fun _ _ => hpow.integrableOn)]
    exact setIntegral_le_integral hpow
      (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (abs_nonneg _) p))
  calc
    _ = ∑ R ∈ T, ∫ x in productBox R,
        Real.rpow (finiteFunctionMaximal (G.filter (fun Q => ∀ i, Q i ≤ R i)) f x) p :=
      integral_rpow_finiteFunctionMaximal_forest T G hdis hcover f p hp0
    _ ≤ ∑ R ∈ T, Real.rpow (p / (p - 1)) (p * (m : ℝ)) *
        ∫ x in productBox R, Real.rpow |f x| p := Finset.sum_le_sum hroot
    _ = Real.rpow (p / (p - 1)) (p * (m : ℝ)) *
        ∑ R ∈ T, ∫ x in productBox R, Real.rpow |f x| p :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hC

/-- Extended power-integral form, with both real integrals proved integrable
before conversion. The coefficient is the p-th power of the norm constant. -/
theorem finite_ordinary_grid_maximal_lintegral
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : ↑G ⊆ gridRectangles D)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    (∫⁻ x, (ENNReal.ofReal (finiteFunctionMaximal G f x)) ^ p) ≤
      (ENNReal.ofReal ((p / (p - 1)) ^ m)) ^ p *
        ∫⁻ x, (ENNReal.ofReal |f x|) ^ p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpow : Integrable (fun x => Real.rpow |f x| p) volume := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le, Real.rpow_eq_pow] using
      hf.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
  have hout := integrable_rpow_finiteFunctionMaximal G f p hp0
  have houtE : (∫⁻ x, (ENNReal.ofReal (finiteFunctionMaximal G f x)) ^ p) =
      ENNReal.ofReal (∫ x, Real.rpow (finiteFunctionMaximal G f x) p) := by
    simp_rw [ENNReal.ofReal_rpow_of_nonneg (finiteFunctionMaximal_nonneg G f _) hp0.le]
    exact (ofReal_integral_eq_lintegral_ofReal hout
      (Filter.Eventually.of_forall (fun x =>
        Real.rpow_nonneg (finiteFunctionMaximal_nonneg G f x) p))).symm
  have hinE : (∫⁻ x, (ENNReal.ofReal |f x|) ^ p) =
      ENNReal.ofReal (∫ x, Real.rpow |f x| p) := by
    simp_rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
    exact (ofReal_integral_eq_lintegral_ofReal hpow
      (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (abs_nonneg _) p))).symm
  have hbase : 0 ≤ p / (p - 1) := div_nonneg hp0.le (sub_pos.mpr hp).le
  have hC : 0 ≤ (p / (p - 1)) ^ m := pow_nonneg hbase m
  have hcoefficient : Real.rpow (p / (p - 1)) (p * (m : ℝ)) =
      Real.rpow ((p / (p - 1)) ^ m) p := by
    simpa only [Real.rpow_eq_pow, mul_comm p (m : ℝ)] using
      (Real.rpow_natCast_mul hbase m p)
  rw [houtE, hinE, ENNReal.ofReal_rpow_of_nonneg hC hp0.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hC p)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [hcoefficient, Real.rpow_eq_pow] using
    finite_ordinary_grid_maximal_integral hd D G hG f p hp hf

/-- The ordinary estimate for the countable family supremum. Grid
countability and the finite-subfamily bounds are derived, not assumed. -/
theorem ordinary_grid_family_maximal_lintegral
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    (∫⁻ x, (familyMaximal G f x) ^ p) ≤
      (ENNReal.ofReal ((p / (p - 1)) ^ m)) ^ p *
        ∫⁻ x, (ENNReal.ofReal |f x|) ^ p := by
  have hc : G.Countable := (countable_gridRectangles D).mono hG
  apply lintegral_familyMaximal_rpow_le G hc f p (zero_lt_one.trans hp)
  intro H
  have hHG : ∀ Q ∈ H.image Subtype.val, Q ∈ G := by
    intro Q hQ
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hQ
    exact R.property
  exact finite_ordinary_grid_maximal_lintegral hd D (H.image Subtype.val)
    (fun Q hQ => hG (hHG Q hQ)) f p hp hf

/-- The extended supremum is finite almost everywhere, before any use of
its real representative. -/
theorem ordinary_grid_family_maximal_ae_finite
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∀ᵐ x ∂volume, familyMaximal G f x < ∞ := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hin : (∫⁻ x, (ENNReal.ofReal |f x|) ^ p) < ∞ := by
    simpa only [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal hp0.le] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top hf.eLpNorm_lt_top
  have hout : (∫⁻ x, (familyMaximal G f x) ^ p) < ∞ :=
    lt_of_le_of_lt (ordinary_grid_family_maximal_lintegral hd D G hG f p hp hf)
      (ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg hp0.le ENNReal.ofReal_ne_top) hin)
  have hc : G.Countable := (countable_gridRectangles D).mono hG
  have ha := ae_lt_top ((measurable_familyMaximal G hc f).pow_const p) hout.ne
  filter_upwards [ha] with x hx
  exact (ENNReal.rpow_lt_top_iff_of_pos hp0).mp hx

/-- Ordinary Lp estimate with exactly `(p / (p - 1)) ^ m` outside the norm.
The whole product grid is obtained by taking `G = gridRectangles D`. -/
theorem ordinary_grid_family_maximal_eLpNorm
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (fun x => (familyMaximal G f x).toReal) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((p / (p - 1)) ^ m) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpE := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hc : G.Countable := (countable_gridRectangles D).mono hG
  have hmM : AEStronglyMeasurable (fun x => (familyMaximal G f x).toReal) volume :=
    (measurable_familyMaximal G hc f).ennreal_toReal.aestronglyMeasurable
  have hfinite := ordinary_grid_family_maximal_ae_finite hd D G hG f p hp hf
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
    (ordinary_grid_family_maximal_lintegral hd D G hG f p hp hf)
      (one_div_nonneg.mpr hp0.le)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp0.le),
    ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] at h
  exact h

/-- Almost-everywhere finiteness of the same ordinary maximum over
Euclidean rectangles, transported by the proved measure-preserving map. -/
theorem ordinary_euclidean_grid_maximal_ae_finite
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∀ᵐ x ∂volume, euclideanFamilyMaximal G f x < ∞ := by
  have hfin := ordinary_grid_family_maximal_ae_finite hd D G hG
    (fun y => f (flattenCoordinates d y)) p hp (memLp_comp_flattenCoordinates f _ hf)
  have hmap := (volume_preserving_flattenCoordinates d).map_eq
  rw [← hmap]
  apply (ae_map_iff (flattenCoordinates d).measurable.aemeasurable
    ((measurable_euclideanFamilyMaximal G ((countable_gridRectangles D).mono hG) f)
      measurableSet_Iio)).mpr
  simpa only [euclideanFamilyMaximal_flatten, Set.mem_Iio] using hfin

/-- The ordinary product maximal inequality in Euclidean coordinates,
with its exact number-of-factors constant and no geometric restriction on G
beyond membership in the specified product grids. -/
theorem ordinary_euclidean_grid_maximal_eLpNorm
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (fun x => (euclideanFamilyMaximal G f x).toReal) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((p / (p - 1)) ^ m) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hmeas := (measurable_euclideanFamilyMaximal G
    ((countable_gridRectangles D).mono hG) f).ennreal_toReal
  rw [← eLpNorm_comp_flattenCoordinates _ _ hmeas.aestronglyMeasurable]
  simp_rw [euclideanFamilyMaximal_flatten]
  exact (ordinary_grid_family_maximal_eLpNorm hd D G hG
    (fun y => f (flattenCoordinates d y)) p hp (memLp_comp_flattenCoordinates f _ hf)).trans_eq
      (congrArg (ENNReal.ofReal ((p / (p - 1)) ^ m) * ·)
        (eLpNorm_comp_flattenCoordinates f _ hf.aestronglyMeasurable))

end ReyZygmund
