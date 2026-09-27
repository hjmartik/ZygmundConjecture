import ReyZygmund.Geometry.ProductSteps
import Mathlib.MeasureTheory.Integral.Marginal

/-! # Lifting a coordinate integral inequality

Fubini for the Lebesgue measures restricted to the coordinate cubes gives the
inequality on the top rectangle. Constancy on the smallest cubes gives
integrability on that rectangle and its slices. Values outside it are
unrestricted.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem restrict_volume_productBox (I : ∀ i, Box (Fin (d i))) :
    volume.restrict (productBox I) =
      Measure.pi (fun i => volume.restrict (I i : Set (Fin (d i) → ℝ))) := by
  exact Measure.restrict_pi_pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
    (fun i => (I i : Set (Fin (d i) → ℝ)))

private theorem productBox_volume_lt_top (I : ∀ i, Box (Fin (d i))) :
    volume (productBox I) < ∞ := by
  change Measure.pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
    (Set.pi Set.univ (fun i => (I i : Set (Fin (d i) → ℝ)))) < ∞
  rw [Measure.pi_pi]
  exact ENNReal.prod_lt_top (fun i _ => (I i).measure_coe_lt_top volume)

private theorem update_mem_productBox (I : ∀ i, Box (Fin (d i)))
    {x : ProductPoint d} (hx : x ∈ productBox I) (j : Fin m)
    {y : Fin (d j) → ℝ} (hy : y ∈ I j) :
    Function.update x j y ∈ productBox I := by
  apply (mem_productBox I _).mpr
  intro i
  by_cases hij : i = j
  · subst i
    simpa using hy
  · simpa [hij] using (mem_productBox I x).mp hx i

private theorem integrableOn_product_leaf (I : ∀ i, Box (Fin (d i)))
    (N : Fin m → ℕ) (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f) :
    IntegrableOn f (productBox I) volume := by
  obtain ⟨A, _, hA⟩ := bounded_product_localization I N f hf
  let : IsFiniteMeasure (volume.restrict (productBox I)) :=
    isFiniteMeasure_restrict.mpr (productBox_volume_lt_top I).ne
  have hloc : IntegrableOn ((productBox I).indicator f) (productBox I) volume :=
    (integrable_const A).mono'
      (measurable_product_localization I N f hf).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs] using hA x))
  exact hloc.congr_fun (fun x hx => Set.indicator_of_mem hx f)
    (measurableSet_productBox I)

private theorem integrableOn_product_leaf_slice (I : ∀ i, Box (Fin (d i)))
    (N : Fin m → ℕ) (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (j : Fin m) {x : ProductPoint d} (hx : x ∈ productBox I) :
    IntegrableOn (fun y => f (Function.update x j y))
      (I j : Set (Fin (d j) → ℝ)) volume := by
  obtain ⟨A, _, hA⟩ := bounded_product_localization I N f hf
  have hloc := integrable_coordinateSlice ((productBox I).indicator f)
    (measurable_product_localization I N f hf) A hA j (I j) x
  exact hloc.congr_fun
    (fun y hy => Set.indicator_of_mem (update_mem_productBox I hx j hy) f)
    (I j).measurableSet_coe

private theorem localized_coordinate_integral_le (I : ∀ i, Box (Fin (d i)))
    (H K : ProductPoint d → ℝ) (C : ℝ) (j : Fin m)
    (hslice : ∀ x ∈ productBox I,
      (∫ y in (I j : Set (Fin (d j) → ℝ)), H (Function.update x j y)) ≤
        C * (∫ y in (I j : Set (Fin (d j) → ℝ)), K (Function.update x j y)))
    (x : ProductPoint d) :
    (∫ y in (I j : Set (Fin (d j) → ℝ)),
      (productBox I).indicator H (Function.update x j y)) ≤
      C * (∫ y in (I j : Set (Fin (d j) → ℝ)),
        (productBox I).indicator K (Function.update x j y)) := by
  by_cases hx : ∀ i, i ≠ j → x i ∈ I i
  · let z := Function.update x j (I j).upper
    have hz : z ∈ productBox I := by
      apply (mem_productBox I z).mpr
      intro i
      by_cases hij : i = j
      · subst i
        simp [z]
      · simpa [z, hij] using hx i hij
    have heq (f : ProductPoint d → ℝ) :
        (∫ y in (I j : Set (Fin (d j) → ℝ)),
          (productBox I).indicator f (Function.update x j y)) =
        ∫ y in (I j : Set (Fin (d j) → ℝ)), f (Function.update z j y) := by
      apply setIntegral_congr_fun (I j).measurableSet_coe
      intro y hy
      have hmem : Function.update x j y ∈ productBox I := by
        simpa only [z, Function.update_idem] using update_mem_productBox I hz j hy
      change (productBox I).indicator f (Function.update x j y) =
        f (Function.update z j y)
      rw [Set.indicator_of_mem hmem]
      simp only [z, Function.update_idem]
    rw [heq H, heq K]
    exact hslice z hz
  · have hnot (y : Fin (d j) → ℝ) : Function.update x j y ∉ productBox I := by
      intro hmem
      apply hx
      intro i hij
      simpa [hij] using (mem_productBox I _).mp hmem i
    have hzero (f : ProductPoint d → ℝ) :
        (∫ y in (I j : Set (Fin (d j) → ℝ)),
          (productBox I).indicator f (Function.update x j y)) = 0 := by
      have heq : (fun y => (productBox I).indicator f (Function.update x j y)) =
          (fun _ : Fin (d j) → ℝ => (0 : ℝ)) :=
        funext (fun y => Set.indicator_of_notMem (hnot y) f)
      rw [heq, integral_zero]
    rw [hzero H, hzero K, mul_zero]

private theorem integral_product_le_of_global_coordinate_le
    (I : ∀ i, Box (Fin (d i))) (F G : ProductPoint d → ℝ)
    (hFm : Measurable F) (hGm : Measurable G)
    (hF0 : ∀ x, 0 ≤ F x) (hG0 : ∀ x, 0 ≤ G x)
    (hFI : IntegrableOn F (productBox I) volume)
    (hGI : IntegrableOn G (productBox I) volume) (j : Fin m)
    (hFs : ∀ x, IntegrableOn (fun y => F (Function.update x j y))
      (I j : Set (Fin (d j) → ℝ)) volume)
    (hGs : ∀ x, IntegrableOn (fun y => G (Function.update x j y))
      (I j : Set (Fin (d j) → ℝ)) volume)
    (hfg : ∀ x,
      (∫ y in (I j : Set (Fin (d j) → ℝ)), F (Function.update x j y)) ≤
        ∫ y in (I j : Set (Fin (d j) → ℝ)), G (Function.update x j y)) :
    (∫ x in productBox I, F x) ≤ ∫ x in productBox I, G x := by
  let μ : ∀ i : Fin m, Measure (Fin (d i) → ℝ) :=
    fun i => volume.restrict (I i : Set (Fin (d i) → ℝ))
  let : ∀ i, IsFiniteMeasure (μ i) := fun i =>
    isFiniteMeasure_restrict.mpr ((I i).measure_coe_lt_top volume).ne
  have hmarginal : lmarginal μ {j} (fun x => ENNReal.ofReal (F x)) ≤
      lmarginal μ {j} (fun x => ENNReal.ofReal (G x)) := by
    simp only [lmarginal_singleton]
    intro x
    change (∫⁻ y in (I j : Set (Fin (d j) → ℝ)),
      ENNReal.ofReal (F (Function.update x j y))) ≤
      ∫⁻ y in (I j : Set (Fin (d j) → ℝ)),
        ENNReal.ofReal (G (Function.update x j y))
    rw [← ofReal_integral_eq_lintegral_ofReal (hFs x)
      (ae_of_all _ (fun y => hF0 _)),
      ← ofReal_integral_eq_lintegral_ofReal (hGs x)
        (ae_of_all _ (fun y => hG0 _))]
    exact ENNReal.ofReal_le_ofReal (hfg x)
  have h := lintegral_le_of_lmarginal_le (μ := μ) {j}
    hFm.ennreal_ofReal hGm.ennreal_ofReal hmarginal
  dsimp only [μ] at h
  rw [← restrict_volume_productBox I,
    ← ofReal_integral_eq_lintegral_ofReal hFI (ae_of_all _ hF0),
    ← ofReal_integral_eq_lintegral_ofReal hGI (ae_of_all _ hG0)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hG0)).mp h

/-- A uniform coordinate-integral inequality gives the inequality on the top
rectangle. Constancy on the smallest cubes gives integrability; values outside the
rectangle are unrestricted. -/
theorem integral_product_le_of_coordinate_le
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (H K : ProductPoint d → ℝ)
    (hH : ProductLeafConstant I N H) (hK : ProductLeafConstant I N K)
    (hH0 : ∀ x ∈ productBox I, 0 ≤ H x)
    (hK0 : ∀ x ∈ productBox I, 0 ≤ K x)
    (C : ℝ) (hC : 0 ≤ C) (j : Fin m)
    (hslice : ∀ x ∈ productBox I,
      (∫ y in (I j : Set (Fin (d j) → ℝ)), H (Function.update x j y)) ≤
        C * (∫ y in (I j : Set (Fin (d j) → ℝ)), K (Function.update x j y))) :
    (∫ x in productBox I, H x) ≤ C * (∫ x in productBox I, K x) := by
  let H₀ := (productBox I).indicator H
  let K₀ := (productBox I).indicator K
  have hHm : Measurable H₀ := measurable_product_localization I N H hH
  have hKm : Measurable K₀ := measurable_product_localization I N K hK
  have hHn : ∀ x, 0 ≤ H₀ x := by
    intro x
    by_cases hx : x ∈ productBox I
    · simpa only [H₀, Set.indicator_of_mem hx] using hH0 x hx
    · simp only [H₀, Set.indicator_of_notMem hx, le_refl]
  have hKn : ∀ x, 0 ≤ K₀ x := by
    intro x
    by_cases hx : x ∈ productBox I
    · simpa only [K₀, Set.indicator_of_mem hx] using hK0 x hx
    · simp only [K₀, Set.indicator_of_notMem hx, le_refl]
  have hHI := integrableOn_product_leaf I N H hH
  have hKI := integrableOn_product_leaf I N K hK
  have hHloc : IntegrableOn H₀ (productBox I) volume :=
    hHI.indicator (measurableSet_productBox I)
  have hKloc : IntegrableOn K₀ (productBox I) volume :=
    hKI.indicator (measurableSet_productBox I)
  obtain ⟨A, _, hA⟩ := bounded_product_localization I N H hH
  obtain ⟨B, _, hB⟩ := bounded_product_localization I N K hK
  have hHs (x : ProductPoint d) :
      IntegrableOn (fun y => H₀ (Function.update x j y))
        (I j : Set (Fin (d j) → ℝ)) volume :=
    integrable_coordinateSlice H₀ hHm A hA j (I j) x
  have hKs (x : ProductPoint d) :
      IntegrableOn (fun y => K₀ (Function.update x j y))
        (I j : Set (Fin (d j) → ℝ)) volume :=
    integrable_coordinateSlice K₀ hKm B hB j (I j) x
  have h := integral_product_le_of_global_coordinate_le I H₀ (fun x => C * K₀ x)
    hHm (measurable_const.mul hKm) hHn (fun x => mul_nonneg hC (hKn x))
    hHloc (hKloc.const_mul C) j hHs (fun x => (hKs x).const_mul C) (by
      intro x
      rw [integral_const_mul]
      exact localized_coordinate_integral_le I H K C j hslice x)
  have heqH : (∫ x in productBox I, H₀ x) = ∫ x in productBox I, H x :=
    setIntegral_congr_fun (measurableSet_productBox I)
      (fun x hx => Set.indicator_of_mem hx H)
  have heqK : (∫ x in productBox I, K₀ x) = ∫ x in productBox I, K x :=
    setIntegral_congr_fun (measurableSet_productBox I)
      (fun x hx => Set.indicator_of_mem hx K)
  simpa only [integral_const_mul, heqH, heqK] using h

end ReyZygmund.Geometry
