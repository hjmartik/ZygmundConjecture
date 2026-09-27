import ReyZygmund.Overlap.Finite
import ReyZygmund.Overlap.Pairing
import ReyZygmund.Maximal.WeakerGlobal

/-! # Analytic preparation for finite sparse-overlap moments -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Overlap

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem memLp_finiteOverlap_power
    (G : Finset (∀ i, Box (Fin (d i)))) (r p : ℝ) (hr : 0 < r) (hp : 0 < p) :
    MemLp (fun x => Real.rpow (finiteOverlap G x) r) (ENNReal.ofReal p) volume := by
  have hm : AEStronglyMeasurable (fun x => Real.rpow (finiteOverlap G x) r) volume :=
    ((Real.continuous_rpow_const hr.le).measurable.comp
      (measurable_finiteOverlap G)).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hm
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top).mp
  convert integrable_rpow_finiteOverlap G (r * p) (mul_pos hr hp) using 1
  funext x
  simp only [Real.norm_of_nonneg (Real.rpow_nonneg (finiteOverlap_nonneg G x) r),
    ENNReal.toReal_ofReal hp.le, Real.rpow_eq_pow,
    ← Real.rpow_mul (finiteOverlap_nonneg G x)]

private theorem eLpNorm_nonneg_eq_root
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (p : ℝ) (hp : 0 < p) (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm f (ENNReal.ofReal p) volume =
      ENNReal.ofReal (Real.rpow (∫ x, Real.rpow (f x) p) (1 / p)) := by
  simpa only [Real.norm_of_nonneg (hf0 _), ENNReal.toReal_ofReal hp.le,
    Real.rpow_eq_pow, one_div] using
    hf.eLpNorm_eq_integral_rpow_norm
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top

private theorem integral_shadow_le_holder
    (G : Finset (∀ i, Box (Fin (d i)))) (p q : ℝ) (hpq : p.HolderConjugate q)
    (F : (Fin (∑ i, d i) → ℝ) → ℝ) (hF0 : ∀ x, 0 ≤ F x)
    (hF : MemLp F (ENNReal.ofReal p) volume) :
    (∫ x in finiteShadow G, F x) ≤
      Real.rpow (∫ x, Real.rpow (F x) p) (1 / p) *
        Real.rpow (volume.real (finiteShadow G)) (1 / q) := by
  let u := (finiteShadow G).indicator (fun _ => (1 : ℝ))
  have hu : MemLp u (ENNReal.ofReal q) volume :=
    memLp_indicator_const _ (measurableSet_finiteShadow G) 1
      (Or.inr (volume_finiteShadow_lt_top G).ne)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall hF0)
    (Filter.Eventually.of_forall (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x))
    hF hu
  have hprod : (fun x => F x * u x) = (finiteShadow G).indicator F := by
    funext x
    by_cases hx : x ∈ finiteShadow G <;> simp [u, hx]
  have hpow : (fun x => (u x) ^ q) = u := by
    funext x
    by_cases hx : x ∈ finiteShadow G
    · simp [u, Set.indicator_of_mem hx]
    · simp [u, Set.indicator_of_notMem hx, Real.zero_rpow hpq.symm.ne_zero]
  rw [hprod, integral_indicator (measurableSet_finiteShadow G), hpow] at h
  simpa only [u, integral_indicator (measurableSet_finiteShadow G),
    integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one,
    Real.rpow_eq_pow] using h

private theorem finite_weaker_maximal_root
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : ↑G ⊆ gridRectangles D)
    (hweak : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i)
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (p : ℝ) (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) volume) :
    MemLp (fun x => (euclideanFamilyMaximal (G : Set _) f x).toReal)
      (ENNReal.ofReal p) volume ∧
    Real.rpow (∫ x, Real.rpow (euclideanFamilyMaximal (G : Set _) f x).toReal p) (1 / p) ≤
      ((maximalDimensionConstant d + 3) * (p / (p - 1)) ^ (m - 1)) *
        Real.rpow (∫ x, Real.rpow (f x) p) (1 / p) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hK : 0 ≤ maximalDimensionConstant d := by
    unfold maximalDimensionConstant
    exact sq_nonneg _
  have hC : 0 ≤ (maximalDimensionConstant d + 3) * (p / (p - 1)) ^ (m - 1) :=
    mul_nonneg (by linarith) (pow_nonneg (div_nonneg hp0.le (sub_pos.mpr hp).le) _)
  have h := euclidean_weaker_grid_maximal_eLpNorm hm hd D (G : Set _) hG hweak f p hp hf
  have hM : MemLp (fun x => (euclideanFamilyMaximal (G : Set _) f x).toReal)
      (ENNReal.ofReal p) volume :=
    h.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)
  refine ⟨hM, ?_⟩
  rw [eLpNorm_nonneg_eq_root _ (fun _ => ENNReal.toReal_nonneg) p hp0 hM,
    eLpNorm_nonneg_eq_root f hf0 p hp0 hf,
    ← ENNReal.ofReal_mul hC] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hC (Real.rpow_nonneg
      (integral_nonneg (fun x => Real.rpow_nonneg (hf0 x) p)) _))).mp h

private theorem moment_cancel
    (J A C eta p q : ℝ) (hJ : 0 ≤ J) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (heta : 0 < eta) (hpq : p.HolderConjugate q)
    (h : eta * J ≤ C * Real.rpow J (1 / p) * Real.rpow A (1 / q)) :
    Real.rpow J (1 / q) ≤ C * eta⁻¹ * Real.rpow A (1 / q) := by
  by_cases hJ0 : J = 0
  · rw [hJ0, Real.rpow_eq_pow, Real.zero_rpow hpq.symm.one_div_ne_zero]
    exact mul_nonneg (mul_nonneg hC (inv_nonneg.mpr heta.le)) (Real.rpow_nonneg hA _)
  have hJpos : 0 < J := lt_of_le_of_ne hJ (Ne.symm hJ0)
  have hfactor : Real.rpow J (1 / q) * Real.rpow J (1 / p) = J := by
    simp only [Real.rpow_eq_pow, one_div]
    rw [← Real.rpow_add hJpos, hpq.symm.inv_add_inv_eq_one, Real.rpow_one]
  have hc : (eta * Real.rpow J (1 / q)) * Real.rpow J (1 / p) ≤
      (C * Real.rpow A (1 / q)) * Real.rpow J (1 / p) := by
    calc
      _ = eta * J := by rw [mul_assoc, hfactor]
      _ ≤ _ := h
      _ = _ := by ring
  have hd := (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hJpos (1 / p))).mp hc
  have hh := mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr heta.le)
  calc
    _ = eta⁻¹ * (eta * Real.rpow J (1 / q)) := by rw [← mul_assoc, inv_mul_cancel₀ heta.ne', one_mul]
    _ ≤ _ := hh
    _ = _ := by ring

private theorem maximal_shadow_holder
    (G : Finset (∀ i, Box (Fin (d i)))) (p q : ℝ) (hpq : p.HolderConjugate q)
    (g : (Fin (∑ i, d i) → ℝ) → ℝ)
    (hM : MemLp (fun x => (euclideanFamilyMaximal (G : Set _) g x).toReal)
      (ENNReal.ofReal p) volume) :
    (∫ x in finiteShadow G, (euclideanFamilyMaximal (G : Set _) g x).toReal) ≤
      Real.rpow (∫ x, Real.rpow (euclideanFamilyMaximal (G : Set _) g x).toReal p) (1 / p) *
        Real.rpow (volume.real (finiteShadow G)) (1 / q) := by
  let M : (Fin (∑ i, d i) → ℝ) → ℝ :=
    fun x => (euclideanFamilyMaximal (G : Set _) g x).toReal
  have hM0 : ∀ x, 0 ≤ M x := fun x =>
    @ENNReal.toReal_nonneg (euclideanFamilyMaximal (G : Set _) g x)
  change (∫ x in finiteShadow G, M x) ≤
    Real.rpow (∫ x, Real.rpow (M x) p) (1 / p) *
      Real.rpow (volume.real (finiteShadow G)) (1 / q)
  exact integral_shadow_le_holder G p q hpq M hM0 hM

/-- Finite sparse overlaps have the paper's exact real-q growth even under
the weaker containment condition. Sparseness supplies measurable
disjoint subsets; all input and output integrability is derived. -/
theorem finite_weaker_sparse_overlap_integral
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : ↑G ⊆ gridRectangles D)
    (hweak : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i)
    (eta : ℝ) (heta : 0 < eta)
    (E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ))
    (hEmeas : ∀ R ∈ G, MeasurableSet (E R))
    (hEsub : ∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)))
    (hEdis : Set.Pairwise (G : Set _) (fun R S => Disjoint (E R) (E S)))
    (hEmass : ∀ R ∈ G, ENNReal.ofReal eta *
      volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤ volume (E R))
    (q : ℝ) (hq : 2 ≤ q) :
    Real.rpow (∫ x, Real.rpow (finiteOverlap G x) q) (1 / q) ≤
      (maximalDimensionConstant d + 3) * eta⁻¹ * q ^ (m - 1) *
        Real.rpow (volume.real (finiteShadow G)) (1 / q) := by
  have hq1 : 1 < q := lt_of_lt_of_le (by norm_num) hq
  let p := Real.conjExponent q
  have hpq : p.HolderConjugate q := (Real.HolderConjugate.conjExponent hq1).symm
  let g := fun x => Real.rpow (finiteOverlap G x) (q - 1)
  let J := ∫ x, Real.rpow (finiteOverlap G x) q
  have hg0 (x) : 0 ≤ g x := Real.rpow_nonneg (finiteOverlap_nonneg G x) _
  have hgp : MemLp g (ENNReal.ofReal p) volume :=
    memLp_finiteOverlap_power G (q - 1) p (sub_pos.mpr hq1) hpq.pos
  have htest : (∫ x, finiteOverlap G x * g x) = J := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    change finiteOverlap G x * Real.rpow (finiteOverlap G x) (q - 1) =
      Real.rpow (finiteOverlap G x) q
    simp only [Real.rpow_eq_pow]
    rw [mul_comm, ← Real.rpow_add_one' (finiteOverlap_nonneg G x) (by linarith : q - 1 + 1 ≠ 0)]
    congr 1
    ring
  have hpower : (∫ x, Real.rpow (g x) p) = J := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    dsimp only [g]
    simp only [Real.rpow_eq_pow, ← Real.rpow_mul (finiteOverlap_nonneg G x),
      hpq.symm.sub_one_mul_conj]
  have hpair := finite_sparse_pairing G eta heta E hEmeas hEsub hEdis hEmass g
    (fun x _ => hg0 x)
    (fun _ _ => (integrable_rpow_finiteOverlap G (q - 1) (sub_pos.mpr hq1)).integrableOn)
  rw [htest] at hpair
  obtain ⟨hM, hmax⟩ := finite_weaker_maximal_root hm hd D G hG hweak g hg0 p hpq.lt hgp
  have hmax' : Real.rpow (∫ x,
      Real.rpow (euclideanFamilyMaximal (G : Set _) g x).toReal p) (1 / p) ≤
      ((maximalDimensionConstant d + 3) * q ^ (m - 1)) * Real.rpow J (1 / p) :=
    hmax.trans_eq (by rw [hpower, ← hpq.conjugate_eq])
  have hh := maximal_shadow_holder G p q hpq g hM
  have hJ : 0 ≤ J := integral_nonneg (fun x => Real.rpow_nonneg (finiteOverlap_nonneg G x) q)
  have hA : 0 ≤ volume.real (finiteShadow G) := measureReal_nonneg
  have hK : 0 ≤ maximalDimensionConstant d := by
    unfold maximalDimensionConstant
    exact sq_nonneg _
  have hC : 0 ≤ (maximalDimensionConstant d + 3) * q ^ (m - 1) :=
    mul_nonneg (by linarith) (pow_nonneg hpq.symm.pos.le _)
  have h := moment_cancel J (volume.real (finiteShadow G))
    ((maximalDimensionConstant d + 3) * q ^ (m - 1)) eta p q hJ hA hC heta hpq
    (hpair.trans (hh.trans (mul_le_mul_of_nonneg_right hmax' (Real.rpow_nonneg hA _))))
  change Real.rpow J (1 / q) ≤ _
  exact h.trans_eq (by ring)

end ReyZygmund.Overlap
