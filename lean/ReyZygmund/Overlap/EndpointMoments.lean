import ReyZygmund.Overlap.Pairing
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FieldSimp

/-! # Finite sparse moments from maximal growth

Assume the maximal estimate for the finite rectangle family. The pairwise disjoint
measurable subsets establishing sparseness then give the moment bound by duality.
A grid or incomparability assumption is not needed for this step.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Overlap

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem measurable_finiteMaximal
    (G : Finset (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) :
    Measurable (fun x => (euclideanFamilyMaximal (G : Set _) f x).toReal) := by
  have h : Measurable (euclideanFamilyMaximal (m := m) (d := d) (G : Set _) f) :=
    measurable_euclideanFamilyMaximal (m := m) (d := d) (G : Set _)
      G.countable_toSet f
  exact Measurable.ennreal_toReal
    (f := euclideanFamilyMaximal (m := m) (d := d) (G : Set _) f) h

private theorem finiteMaximal_nonneg
    (G : Finset (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (x : Fin (∑ i, d i) → ℝ) :
    0 ≤ (euclideanFamilyMaximal (G : Set _) f x).toReal :=
  @ENNReal.toReal_nonneg (euclideanFamilyMaximal (m := m) (d := d) (G : Set _) f x)

private theorem integrable_finiteMaximal_rpow
    (G : Finset (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ) (hp : 0 < p) :
    Integrable (fun x => Real.rpow
      (euclideanFamilyMaximal (G : Set _) f x).toReal p) volume := by
  have hmeas : Measurable (fun x => Real.rpow
      (euclideanFamilyMaximal (G : Set _) f x).toReal p) :=
    (Real.continuous_rpow_const hp.le).measurable.comp
      (measurable_finiteMaximal (m := m) (d := d) G f)
  apply ((volume_preserving_flattenCoordinates d).integrable_comp
    hmeas.aestronglyMeasurable).mp
  have hi := integrable_rpow_finiteFunctionMaximal G
    (fun y => f (flattenCoordinates d y)) p hp
  change Integrable (fun x => Real.rpow
    (euclideanFamilyMaximal (G : Set _) f (flattenCoordinates d x)).toReal p) volume
  simp_rw [euclideanFamilyMaximal_flatten, familyMaximal_coe_finset,
    ENNReal.toReal_ofReal (finiteFunctionMaximal_nonneg _ _ _)]
  exact hi

private theorem memLp_finiteMaximal
    (G : Finset (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ) (hp : 0 < p) :
    MemLp (fun x => (euclideanFamilyMaximal (G : Set _) f x).toReal)
      (ENNReal.ofReal p) volume := by
  let M : (Fin (∑ i, d i) → ℝ) → ℝ :=
    fun x => (euclideanFamilyMaximal (G : Set _) f x).toReal
  have hM : Measurable M := measurable_finiteMaximal (m := m) (d := d) G f
  have hm : AEStronglyMeasurable M volume := hM.aestronglyMeasurable
  have hM0 : ∀ x, 0 ≤ M x := finiteMaximal_nonneg (m := m) (d := d) G f
  change MemLp M (ENNReal.ofReal p) volume
  apply (integrable_norm_rpow_iff (f := M) (μ := volume) hm
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top).mp
  simpa only [Real.norm_of_nonneg (hM0 _),
    ENNReal.toReal_ofReal hp.le, Real.rpow_eq_pow] using
      integrable_finiteMaximal_rpow (m := m) (d := d) G f p hp

private theorem root_le_of_finite_maximal_power
    (G : Finset (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (p B : ℝ) (hp : 0 < p) (hB : 0 ≤ B)
    (hfi : Integrable (fun x => Real.rpow (f x) p) volume)
    (hbound : (∫⁻ x, ENNReal.ofReal (Real.rpow
        (euclideanFamilyMaximal (G : Set _) f x).toReal p)) ≤
      ENNReal.ofReal (Real.rpow B p) * ∫⁻ x, ENNReal.ofReal (Real.rpow (f x) p)) :
    Real.rpow (∫ x, Real.rpow
        (euclideanFamilyMaximal (G : Set _) f x).toReal p) (1 / p) ≤
      B * Real.rpow (∫ x, Real.rpow (f x) p) (1 / p) := by
  have hM := ofReal_integral_eq_lintegral_ofReal
    (integrable_finiteMaximal_rpow (m := m) (d := d) G f p hp)
    (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg
      (finiteMaximal_nonneg (m := m) (d := d) G f x) p))
  have hf := ofReal_integral_eq_lintegral_ofReal hfi
    (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (hf0 x) p))
  have hmul : ENNReal.ofReal
      (Real.rpow B p * ∫ x, Real.rpow (f x) p) =
      ENNReal.ofReal (Real.rpow B p) *
        ENNReal.ofReal (∫ x, Real.rpow (f x) p) :=
    ENNReal.ofReal_mul (Real.rpow_nonneg hB p)
  rw [← hM, ← hf, ← hmul] at hbound
  have hI : 0 ≤ ∫ x, Real.rpow (f x) p :=
    integral_nonneg (fun x => Real.rpow_nonneg (hf0 x) p)
  have hJ : 0 ≤ ∫ x, Real.rpow
      (euclideanFamilyMaximal (G : Set _) f x).toReal p :=
    integral_nonneg (fun x => Real.rpow_nonneg
      (finiteMaximal_nonneg (m := m) (d := d) G f x) p)
  have hb := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.rpow_nonneg hB p) hI)).mp hbound
  have hr := Real.rpow_le_rpow hJ hb (one_div_nonneg.mpr hp.le)
  simp only [Real.rpow_eq_pow, one_div] at hr hI hJ ⊢
  rw [Real.mul_rpow (Real.rpow_nonneg hB p) hI,
    Real.rpow_rpow_inv hB hp.ne'] at hr
  exact hr

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
  have hM0 : ∀ x, 0 ≤ M x := finiteMaximal_nonneg (m := m) (d := d) G g
  change (∫ x in finiteShadow G, M x) ≤
    Real.rpow (∫ x, Real.rpow (M x) p) (1 / p) *
      Real.rpow (volume.real (finiteShadow G)) (1 / q)
  exact integral_shadow_le_holder (m := m) (d := d) G p q hpq M hM0 hM

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

/-- Finite sparse overlaps inherit the displayed real-q growth from a
conditional strong estimate for their own finite maximal function. -/
theorem finite_endpoint_sparse_overlap_integral
    (G : Finset (∀ i, Box (Fin (d i)))) (eta : ℝ) (heta : 0 < eta)
    (E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ))
    (hEmeas : ∀ R ∈ G, MeasurableSet (E R))
    (hEsub : ∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)))
    (hEdis : Set.Pairwise (G : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (E R) (E S)))
    (hEmass : ∀ R ∈ G, ENNReal.ofReal eta *
      volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤ volume (E R))
    (k : ℕ) (C : ℝ) (hC : 0 < C)
    (hstrong : ∀ f : (Fin (∑ i, d i) → ℝ) → ℝ,
      LocallyIntegrable f volume → Measurable f → (∀ x, 0 ≤ f x) →
      ∀ p : ℝ, 1 < p → p ≤ 2 →
        (∫⁻ x, ENNReal.ofReal (Real.rpow
          (euclideanFamilyMaximal (G : Set _) f x).toReal p)) ≤
          ENNReal.ofReal (Real.rpow (C / (p - 1) ^ k) p) *
            ∫⁻ x, ENNReal.ofReal (Real.rpow (f x) p))
    (q : ℝ) (hq : 2 ≤ q) :
    Real.rpow (∫ x, Real.rpow (finiteOverlap G x) q) (1 / q) ≤
      C * eta⁻¹ * q ^ k * Real.rpow (volume.real (finiteShadow G)) (1 / q) := by
  have hq1 : 1 < q := lt_of_lt_of_le (by norm_num) hq
  have hq0 : 0 < q := zero_lt_one.trans hq1
  let p : ℝ := Real.conjExponent q
  have hpq : p.HolderConjugate q := (Real.HolderConjugate.conjExponent hq1).symm
  have hp2 : p ≤ 2 := by
    change q / (q - 1) ≤ 2
    apply (div_le_iff₀ (sub_pos.mpr hq1)).mpr
    linarith
  have hinv : (p - 1)⁻¹ = q - 1 := by
    apply inv_eq_of_mul_eq_one_right
    nlinarith [hpq.mul_eq_add]
  have hcoef : C / (p - 1) ^ k ≤ C * q ^ k := by
    rw [div_eq_mul_inv, ← inv_pow, hinv]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (sub_nonneg.mpr hq1.le) (by linarith : q - 1 ≤ q) k) hC.le
  let g : (Fin (∑ i, d i) → ℝ) → ℝ :=
    fun x => Real.rpow (finiteOverlap G x) (q - 1)
  let J : ℝ := ∫ x, Real.rpow (finiteOverlap G x) q
  have hg0 (x) : 0 ≤ g x := Real.rpow_nonneg (finiteOverlap_nonneg G x) _
  have hgm : Measurable g :=
    (Real.continuous_rpow_const (sub_nonneg.mpr hq1.le)).measurable.comp
      (measurable_finiteOverlap G)
  have hgi : Integrable g volume :=
    integrable_rpow_finiteOverlap G (q - 1) (sub_pos.mpr hq1)
  have hgpower : (fun x => Real.rpow (g x) p) =
      (fun x => Real.rpow (finiteOverlap G x) q) := by
    funext x
    dsimp only [g]
    simp only [Real.rpow_eq_pow, ← Real.rpow_mul (finiteOverlap_nonneg G x),
      hpq.symm.sub_one_mul_conj]
  have hgpi : Integrable (fun x => Real.rpow (g x) p) volume := by
    rw [hgpower]
    exact integrable_rpow_finiteOverlap G q hq0
  have hpower : (∫ x, Real.rpow (g x) p) = J := by
    change (∫ x, Real.rpow (g x) p) = ∫ x, Real.rpow (finiteOverlap G x) q
    rw [hgpower]
  have htest : (∫ x, finiteOverlap G x * g x) = J := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    change finiteOverlap G x * Real.rpow (finiteOverlap G x) (q - 1) =
      Real.rpow (finiteOverlap G x) q
    simp only [Real.rpow_eq_pow]
    rw [mul_comm, ← Real.rpow_add_one' (finiteOverlap_nonneg G x)
      (by linarith : q - 1 + 1 ≠ 0)]
    congr 1
    ring
  have hpair := finite_sparse_pairing G eta heta E hEmeas hEsub hEdis hEmass g
    (fun x _ => hg0 x) (fun _ _ => hgi.integrableOn)
  rw [htest] at hpair
  have hJ : 0 ≤ J :=
    integral_nonneg (fun x => Real.rpow_nonneg (finiteOverlap_nonneg G x) q)
  have hA : 0 ≤ volume.real (finiteShadow G) := measureReal_nonneg
  have hB : 0 ≤ C / (p - 1) ^ k :=
    div_nonneg hC.le (pow_nonneg hpq.sub_one_pos.le _)
  have hmax := root_le_of_finite_maximal_power (m := m) (d := d) G g hg0 p
    (C / (p - 1) ^ k) hpq.pos hB hgpi
    (hstrong g hgi.locallyIntegrable hgm hg0 p hpq.lt hp2)
  have hmax' : Real.rpow (∫ x, Real.rpow
      (euclideanFamilyMaximal (G : Set _) g x).toReal p) (1 / p) ≤
      (C * q ^ k) * Real.rpow J (1 / p) := by
    rw [hpower] at hmax
    exact hmax.trans (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hJ _))
  have hmem : MemLp (fun x => (euclideanFamilyMaximal (G : Set _) g x).toReal)
      (ENNReal.ofReal p) volume :=
    memLp_finiteMaximal (m := m) (d := d) G g p hpq.pos
  have hh := maximal_shadow_holder (m := m) (d := d) G p q hpq g hmem
  have hCq : 0 ≤ C * q ^ k := mul_nonneg hC.le (pow_nonneg hq0.le _)
  have h := moment_cancel J (volume.real (finiteShadow G)) (C * q ^ k)
    eta p q hJ hA hCq heta hpq
    (hpair.trans (hh.trans (mul_le_mul_of_nonneg_right hmax' (Real.rpow_nonneg hA _))))
  change Real.rpow J (1 / q) ≤ _
  exact h.trans_eq (by ring)

/-- The same conditional sparse moment bound in the extended-integral form
used for finite-family limits. All real-integral conversions use integrability. -/
theorem finite_endpoint_sparse_overlap_lintegral
    (G : Finset (∀ i, Box (Fin (d i)))) (eta : ℝ) (heta : 0 < eta)
    (E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ))
    (hEmeas : ∀ R ∈ G, MeasurableSet (E R))
    (hEsub : ∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)))
    (hEdis : Set.Pairwise (G : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (E R) (E S)))
    (hEmass : ∀ R ∈ G, ENNReal.ofReal eta *
      volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤ volume (E R))
    (k : ℕ) (C : ℝ) (hC : 0 < C)
    (hstrong : ∀ f : (Fin (∑ i, d i) → ℝ) → ℝ,
      LocallyIntegrable f volume → Measurable f → (∀ x, 0 ≤ f x) →
      ∀ p : ℝ, 1 < p → p ≤ 2 →
        (∫⁻ x, ENNReal.ofReal (Real.rpow
          (euclideanFamilyMaximal (G : Set _) f x).toReal p)) ≤
          ENNReal.ofReal (Real.rpow (C / (p - 1) ^ k) p) *
            ∫⁻ x, ENNReal.ofReal (Real.rpow (f x) p))
    (q : ℝ) (hq : 2 ≤ q) :
    (∫⁻ x, (ENNReal.ofReal (finiteOverlap G x)) ^ q) ≤
      (ENNReal.ofReal (C * eta⁻¹ * q ^ k)) ^ q * volume (finiteShadow G) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hJ : 0 ≤ ∫ x, Real.rpow (finiteOverlap G x) q :=
    integral_nonneg (fun x => Real.rpow_nonneg (finiteOverlap_nonneg G x) q)
  have hA : 0 ≤ volume.real (finiteShadow G) := measureReal_nonneg
  have hcoef : 0 ≤ C * eta⁻¹ * q ^ k :=
    mul_nonneg (mul_nonneg hC.le (inv_nonneg.mpr heta.le)) (pow_nonneg hq0.le _)
  have h := finite_endpoint_sparse_overlap_integral G eta heta E hEmeas hEsub hEdis
    hEmass k C hC hstrong q hq
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hJ _) h hq0.le
  simp only [Real.rpow_eq_pow, one_div] at hh hJ
  rw [Real.rpow_inv_rpow hJ hq0.ne',
    Real.mul_rpow hcoef (Real.rpow_nonneg hA _), Real.rpow_inv_rpow hA hq0.ne'] at hh
  have hE : (∫⁻ x, (ENNReal.ofReal (finiteOverlap G x)) ^ q) =
      ENNReal.ofReal (∫ x, Real.rpow (finiteOverlap G x) q) := by
    simp_rw [ENNReal.ofReal_rpow_of_nonneg (finiteOverlap_nonneg G _) hq0.le]
    exact (ofReal_integral_eq_lintegral_ofReal (integrable_rpow_finiteOverlap G q hq0)
      (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (finiteOverlap_nonneg G x) q))).symm
  rw [hE, ENNReal.ofReal_rpow_of_nonneg hcoef hq0.le,
    ← ofReal_measureReal (volume_finiteShadow_lt_top G).ne,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hcoef q)]
  simpa only [Real.rpow_eq_pow] using ENNReal.ofReal_le_ofReal hh

end ReyZygmund.Overlap
