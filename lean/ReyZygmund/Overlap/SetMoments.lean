import ReyZygmund.Overlap.SetPairing
import Mathlib.Tactic.FieldSimp

/-! # Exact finite sparse moments from measurable-set maximal growth

The test overlap^(q-1) has finite-measure support, not necessarily bounded
spatial support. Holder duality keeps the exact conjugate factor (q-1)^k.
-/

open MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Overlap

variable {d : ℕ}

private theorem root_le_of_extended_power
    (M : (Fin d → ℝ) → ℝ≥0∞) (hMt : ∀ x, M x < ∞)
    (f : (Fin d → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (p B : ℝ) (hp : 0 < p) (hB : 0 ≤ B)
    (hMi : Integrable (fun x => Real.rpow (M x).toReal p) volume)
    (hfi : Integrable (fun x => Real.rpow (f x) p) volume)
    (hbound : (∫⁻ x, (M x) ^ p) ≤
      (ENNReal.ofReal B) ^ p * ∫⁻ x, (ENNReal.ofReal |f x|) ^ p) :
    Real.rpow (∫ x, Real.rpow (M x).toReal p) (1 / p) ≤
      B * Real.rpow (∫ x, Real.rpow (f x) p) (1 / p) := by
  have hMeq (x) : (M x) ^ p = ENNReal.ofReal (Real.rpow (M x).toReal p) := by
    simp only [Real.rpow_eq_pow]
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le,
      ENNReal.ofReal_toReal (hMt x).ne]
  simp_rw [hMeq, abs_of_nonneg (hf0 _),
    ENNReal.ofReal_rpow_of_nonneg (hf0 _) hp.le,
    ENNReal.ofReal_rpow_of_nonneg hB hp.le] at hbound
  have hM := ofReal_integral_eq_lintegral_ofReal hMi
    (Filter.Eventually.of_forall (fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg p))
  have hf := ofReal_integral_eq_lintegral_ofReal hfi
    (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (hf0 x) p))
  have hmul : ENNReal.ofReal (Real.rpow B p * ∫ x, Real.rpow (f x) p) =
      ENNReal.ofReal (Real.rpow B p) *
        ENNReal.ofReal (∫ x, Real.rpow (f x) p) :=
    ENNReal.ofReal_mul (Real.rpow_nonneg hB p)
  simp only [Real.rpow_eq_pow] at hM hf hmul hbound
  rw [← hM, ← hf, ← hmul] at hbound
  have hI : 0 ≤ ∫ x, Real.rpow (f x) p :=
    integral_nonneg (fun x => Real.rpow_nonneg (hf0 x) p)
  have hJ : 0 ≤ ∫ x, Real.rpow (M x).toReal p :=
    integral_nonneg (fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg p)
  have hb := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.rpow_nonneg hB p) hI)).mp hbound
  have hr := Real.rpow_le_rpow hJ hb (one_div_nonneg.mpr hp.le)
  simp only [Real.rpow_eq_pow, one_div] at hr hI hJ ⊢
  rw [Real.mul_rpow (Real.rpow_nonneg hB p) hI,
    Real.rpow_rpow_inv hB hp.ne'] at hr
  exact hr

private theorem finite_set_maximal_power_root
    (H : Finset (Set (Fin d → ℝ))) (hm : ∀ I ∈ H, MeasurableSet I)
    (hpos : ∀ I ∈ H, 0 < volume I) (hfin : ∀ I ∈ H, volume I < ∞)
    (f : (Fin d → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f volume)
    (p B : ℝ) (hp : 0 < p) (hB : 0 ≤ B)
    (hfpi : Integrable (fun x => Real.rpow (f x) p) volume)
    (hbound : (∫⁻ x, (setFamilyMaximal (H : Set _) f x) ^ p) ≤
      (ENNReal.ofReal B) ^ p * ∫⁻ x, (ENNReal.ofReal |f x|) ^ p) :
    Real.rpow (∫ x, Real.rpow (setFamilyMaximal (H : Set _) f x).toReal p) (1 / p) ≤
      B * Real.rpow (∫ x, Real.rpow (f x) p) (1 / p) := by
  have hMt : ∀ x, setFamilyMaximal (H : Set _) f x < ∞ :=
    setFamilyMaximal_finset_lt_top H hpos hfin f (fun _ _ => hfi.integrableOn)
  have hmem : MemLp (fun x => (setFamilyMaximal (H : Set _) f x).toReal)
      (ENNReal.ofReal p) volume :=
    memLp_setFamilyMaximal_finset H hm hpos hfin f (fun _ _ => hfi.integrableOn) _
  -- Abstract this exact function before real-power unification, which otherwise
  -- repeatedly unfolds the defining supremum during elaboration.
  generalize hM : setFamilyMaximal (d := d) (H : Set _) f = M at hMt hmem hbound ⊢
  have hMi : Integrable (fun x => Real.rpow (M x).toReal p) volume := by
    have hi := hmem.integrable_norm_rpow
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
    simpa only [Real.norm_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.toReal_ofReal hp.le, Real.rpow_eq_pow] using hi
  exact root_le_of_extended_power (d := d) M hMt f hf0 p B hp hB hMi hfpi hbound

private theorem integral_setShadow_le_holder
    (H : Finset (Set (Fin d → ℝ))) (hm : ∀ I ∈ H, MeasurableSet I)
    (hfin : ∀ I ∈ H, volume I < ∞)
    (p q : ℝ) (hpq : p.HolderConjugate q)
    (F : (Fin d → ℝ) → ℝ) (hF0 : ∀ x, 0 ≤ F x)
    (hF : MemLp F (ENNReal.ofReal p) volume) :
    (∫ x in finiteSetShadow H, F x) ≤
      Real.rpow (∫ x, Real.rpow (F x) p) (1 / p) *
        Real.rpow (volume.real (finiteSetShadow H)) (1 / q) := by
  let u := (finiteSetShadow H).indicator (fun _ => (1 : ℝ))
  have hu : MemLp u (ENNReal.ofReal q) volume :=
    memLp_indicator_const _ (measurableSet_finiteSetShadow H hm) 1
      (Or.inr (volume_finiteSetShadow_lt_top H hfin).ne)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall hF0)
    (Filter.Eventually.of_forall (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x))
    hF hu
  have hprod : (fun x => F x * u x) = (finiteSetShadow H).indicator F := by
    funext x
    by_cases hx : x ∈ finiteSetShadow H <;> simp [u, hx]
  have hpow : (fun x => (u x) ^ q) = u := by
    funext x
    by_cases hx : x ∈ finiteSetShadow H
    · simp [u, Set.indicator_of_mem hx]
    · simp [u, Set.indicator_of_notMem hx, Real.zero_rpow hpq.symm.ne_zero]
  rw [hprod, integral_indicator (measurableSet_finiteSetShadow H hm), hpow] at h
  simpa only [u, integral_indicator (measurableSet_finiteSetShadow H hm),
    integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one,
    Real.rpow_eq_pow] using h

private theorem finite_set_maximal_shadow_holder
    (H : Finset (Set (Fin d → ℝ))) (hm : ∀ I ∈ H, MeasurableSet I)
    (hfin : ∀ I ∈ H, volume I < ∞)
    (p q : ℝ) (hpq : p.HolderConjugate q) (g : (Fin d → ℝ) → ℝ)
    (hmem : MemLp (fun x => (setFamilyMaximal (H : Set _) g x).toReal)
      (ENNReal.ofReal p) volume) :
    (∫ x in finiteSetShadow H, (setFamilyMaximal (H : Set _) g x).toReal) ≤
      Real.rpow (∫ x, Real.rpow (setFamilyMaximal (H : Set _) g x).toReal p) (1 / p) *
        Real.rpow (volume.real (finiteSetShadow H)) (1 / q) := by
  generalize hM : setFamilyMaximal (d := d) (H : Set _) g = M at hmem ⊢
  exact integral_setShadow_le_holder (d := d) H hm hfin p q hpq
    (fun x => (M x).toReal) (fun x => @ENNReal.toReal_nonneg (M x)) hmem

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
    _ = eta⁻¹ * (eta * Real.rpow J (1 / q)) := by
      rw [← mul_assoc, inv_mul_cancel₀ heta.ne', one_mul]
    _ ≤ _ := hh
    _ = _ := by ring

private theorem conjugate_exponent_facts (q : ℝ) (hq : 2 ≤ q) :
    (Real.conjExponent q).HolderConjugate q ∧ Real.conjExponent q ≤ 2 ∧
      (Real.conjExponent q - 1)⁻¹ = q - 1 := by
  have hq1 : 1 < q := lt_of_lt_of_le (by norm_num) hq
  have hpq := (Real.HolderConjugate.conjExponent hq1).symm
  refine ⟨hpq, ?_, ?_⟩
  · change q / (q - 1) ≤ 2
    apply (div_le_iff₀ (sub_pos.mpr hq1)).mpr
    linarith
  · apply inv_eq_of_mul_eq_one_right
    nlinarith [hpq.mul_eq_add]

private theorem overlap_test_facts
    (H : Finset (Set (Fin d → ℝ))) (hm : ∀ I ∈ H, MeasurableSet I)
    (hfin : ∀ I ∈ H, volume I < ∞) (p q : ℝ) (hpq : p.HolderConjugate q) :
    let g : (Fin d → ℝ) → ℝ := fun x => Real.rpow (finiteSetOverlap H x) (q - 1)
    Measurable g ∧ (∀ x, 0 ≤ g x) ∧ Integrable g volume ∧
      Integrable (fun x => Real.rpow (g x) p) volume ∧
      (∫ x, Real.rpow (g x) p) = (∫ x, Real.rpow (finiteSetOverlap H x) q) ∧
      (∫ x, finiteSetOverlap H x * g x) = ∫ x, Real.rpow (finiteSetOverlap H x) q := by
  let g : (Fin d → ℝ) → ℝ := fun x => Real.rpow (finiteSetOverlap H x) (q - 1)
  have hg0 (x) : 0 ≤ g x := Real.rpow_nonneg (finiteSetOverlap_nonneg H x) _
  have hgm : Measurable g :=
    (Real.continuous_rpow_const hpq.symm.sub_one_pos.le).measurable.comp
      (measurable_finiteSetOverlap H hm)
  have hgi : Integrable g volume :=
    integrable_rpow_finiteSetOverlap H hm hfin (q - 1) hpq.symm.sub_one_pos
  have hgpower : (fun x => Real.rpow (g x) p) =
      (fun x => Real.rpow (finiteSetOverlap H x) q) := by
    funext x
    dsimp only [g]
    simp only [Real.rpow_eq_pow, ← Real.rpow_mul (finiteSetOverlap_nonneg H x),
      hpq.symm.sub_one_mul_conj]
  have hgpi : Integrable (fun x => Real.rpow (g x) p) volume := by
    rw [hgpower]
    exact integrable_rpow_finiteSetOverlap H hm hfin q hpq.symm.pos
  refine ⟨hgm, hg0, hgi, hgpi, ?_, ?_⟩
  · rw [hgpower]
  · apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    change finiteSetOverlap H x * Real.rpow (finiteSetOverlap H x) (q - 1) =
      Real.rpow (finiteSetOverlap H x) q
    simp only [Real.rpow_eq_pow]
    rw [mul_comm, ← Real.rpow_add_one' (finiteSetOverlap_nonneg H x)
      (by linarith [hpq.symm.pos] : q - 1 + 1 ≠ 0)]
    congr 1
    ring

private theorem sparse_pairing_power_bound
    (H : Finset (Set (Fin d → ℝ))) (hm : ∀ I ∈ H, MeasurableSet I)
    (hpos : ∀ I ∈ H, 0 < volume I) (hfin : ∀ I ∈ H, volume I < ∞)
    (eta : ℝ) (heta : 0 < eta)
    (E : Set (Fin d → ℝ) → Set (Fin d → ℝ))
    (hEmeas : ∀ I ∈ H, MeasurableSet (E I)) (hEsub : ∀ I ∈ H, E I ⊆ I)
    (hEdis : Set.Pairwise (H : Set (Set (Fin d → ℝ)))
      (fun I J => Disjoint (E I) (E J)))
    (hEmass : ∀ I ∈ H, ENNReal.ofReal eta * volume I ≤ volume (E I))
    (g : (Fin d → ℝ) → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g volume)
    (p q : ℝ) (hpq : p.HolderConjugate q) (B : ℝ) (hB : 0 ≤ B)
    (hgpi : Integrable (fun x => Real.rpow (g x) p) volume)
    (hbound : (∫⁻ x, (setFamilyMaximal (H : Set _) g x) ^ p) ≤
      (ENNReal.ofReal B) ^ p * ∫⁻ x, (ENNReal.ofReal |g x|) ^ p) :
    eta * (∫ x, finiteSetOverlap H x * g x) ≤
      B * Real.rpow (∫ x, Real.rpow (g x) p) (1 / p) *
        Real.rpow (volume.real (finiteSetShadow H)) (1 / q) := by
  have hpair := finite_set_sparse_pairing H hm hpos hfin eta heta E hEmeas hEsub hEdis
    hEmass g (fun x _ => hg0 x) (fun _ _ => hgi.integrableOn)
  have hmem : MemLp (fun x => (setFamilyMaximal (H : Set _) g x).toReal)
      (ENNReal.ofReal p) volume :=
    memLp_setFamilyMaximal_finset H hm hpos hfin g (fun _ _ => hgi.integrableOn) _
  have hmax := finite_set_maximal_power_root (d := d) H hm hpos hfin g hg0 hgi
    p B hpq.pos hB hgpi hbound
  have hh := finite_set_maximal_shadow_holder (d := d) H hm hfin p q hpq g hmem
  exact hpair.trans (hh.trans
    (mul_le_mul_of_nonneg_right hmax (Real.rpow_nonneg measureReal_nonneg _)))

/-- Sparse duality for finite measurable-set families, with the exact
factor (q-1)^k inherited from the conjugate maximal exponent. -/
theorem finite_set_sparse_overlap_integral
    (H : Finset (Set (Fin d → ℝ))) (hm : ∀ I ∈ H, MeasurableSet I)
    (hpos : ∀ I ∈ H, 0 < volume I) (hfin : ∀ I ∈ H, volume I < ∞)
    (eta : ℝ) (heta : 0 < eta)
    (E : Set (Fin d → ℝ) → Set (Fin d → ℝ))
    (hEmeas : ∀ I ∈ H, MeasurableSet (E I)) (hEsub : ∀ I ∈ H, E I ⊆ I)
    (hEdis : Set.Pairwise (H : Set (Set (Fin d → ℝ)))
      (fun I J => Disjoint (E I) (E J)))
    (hEmass : ∀ I ∈ H, ENNReal.ofReal eta * volume I ≤ volume (E I))
    (k : ℕ) (C : ℝ) (hC : 0 < C)
    (hstrong : ∀ f : (Fin d → ℝ) → ℝ,
      Measurable f → (∀ x, 0 ≤ f x) → ∀ p : ℝ, 1 < p → p ≤ 2 →
        (∫⁻ x, (setFamilyMaximal (H : Set _) f x) ^ p) ≤
          (ENNReal.ofReal (C / (p - 1) ^ k)) ^ p *
            ∫⁻ x, (ENNReal.ofReal |f x|) ^ p)
    (q : ℝ) (hq : 2 ≤ q) :
    Real.rpow (∫ x, Real.rpow (finiteSetOverlap H x) q) (1 / q) ≤
      C * eta⁻¹ * (q - 1) ^ k *
        Real.rpow (volume.real (finiteSetShadow H)) (1 / q) := by
  have hq1 : 1 < q := lt_of_lt_of_le (by norm_num) hq
  let p : ℝ := Real.conjExponent q
  obtain ⟨hpq, hp2, hinv⟩ := conjugate_exponent_facts q hq
  have hcoef : C / (p - 1) ^ k = C * (q - 1) ^ k := by
    rw [div_eq_mul_inv, ← inv_pow, hinv]
  let g : (Fin d → ℝ) → ℝ := fun x => Real.rpow (finiteSetOverlap H x) (q - 1)
  let J : ℝ := ∫ x, Real.rpow (finiteSetOverlap H x) q
  obtain ⟨hgm, hg0, hgi, hgpi, hpower, htest⟩ := overlap_test_facts H hm hfin p q hpq
  have hB : 0 ≤ C / (p - 1) ^ k :=
    div_nonneg hC.le (pow_nonneg hpq.sub_one_pos.le _)
  have hpair := sparse_pairing_power_bound H hm hpos hfin eta heta E hEmeas hEsub hEdis
    hEmass g hg0 hgi p q hpq (C / (p - 1) ^ k) hB hgpi
    (hstrong g hgm hg0 p hpq.lt hp2)
  rw [htest, hpower, hcoef] at hpair
  have hJ : 0 ≤ J :=
    integral_nonneg (fun x => Real.rpow_nonneg (finiteSetOverlap_nonneg H x) q)
  have hA : 0 ≤ volume.real (finiteSetShadow H) := measureReal_nonneg
  have hCq : 0 ≤ C * (q - 1) ^ k :=
    mul_nonneg hC.le (pow_nonneg (sub_nonneg.mpr hq1.le) _)
  have h := moment_cancel J (volume.real (finiteSetShadow H)) (C * (q - 1) ^ k)
    eta p q hJ hA hCq heta hpq hpair
  change Real.rpow J (1 / q) ≤ _
  exact h.trans_eq (by ring)

/-- The extended-integral moment estimate used for finite-family limits. Integrability
justifies the real integrals, and the q = 2 coefficient is C/eta. -/
theorem finite_set_sparse_overlap_lintegral
    (H : Finset (Set (Fin d → ℝ))) (hm : ∀ I ∈ H, MeasurableSet I)
    (hpos : ∀ I ∈ H, 0 < volume I) (hfin : ∀ I ∈ H, volume I < ∞)
    (eta : ℝ) (heta : 0 < eta)
    (E : Set (Fin d → ℝ) → Set (Fin d → ℝ))
    (hEmeas : ∀ I ∈ H, MeasurableSet (E I)) (hEsub : ∀ I ∈ H, E I ⊆ I)
    (hEdis : Set.Pairwise (H : Set (Set (Fin d → ℝ)))
      (fun I J => Disjoint (E I) (E J)))
    (hEmass : ∀ I ∈ H, ENNReal.ofReal eta * volume I ≤ volume (E I))
    (k : ℕ) (C : ℝ) (hC : 0 < C)
    (hstrong : ∀ f : (Fin d → ℝ) → ℝ,
      Measurable f → (∀ x, 0 ≤ f x) → ∀ p : ℝ, 1 < p → p ≤ 2 →
        (∫⁻ x, (setFamilyMaximal (H : Set _) f x) ^ p) ≤
          (ENNReal.ofReal (C / (p - 1) ^ k)) ^ p *
            ∫⁻ x, (ENNReal.ofReal |f x|) ^ p)
    (q : ℝ) (hq : 2 ≤ q) :
    (∫⁻ x, (ENNReal.ofReal (finiteSetOverlap H x)) ^ q) ≤
      (ENNReal.ofReal (C * eta⁻¹ * (q - 1) ^ k)) ^ q * volume (finiteSetShadow H) := by
  have hq1 : 1 < q := lt_of_lt_of_le (by norm_num) hq
  have hq0 : 0 < q := zero_lt_one.trans hq1
  have hJ : 0 ≤ ∫ x, Real.rpow (finiteSetOverlap H x) q :=
    integral_nonneg (fun x => Real.rpow_nonneg (finiteSetOverlap_nonneg H x) q)
  have hA : 0 ≤ volume.real (finiteSetShadow H) := measureReal_nonneg
  have hcoef : 0 ≤ C * eta⁻¹ * (q - 1) ^ k :=
    mul_nonneg (mul_nonneg hC.le (inv_nonneg.mpr heta.le))
      (pow_nonneg (sub_nonneg.mpr hq1.le) _)
  have h := finite_set_sparse_overlap_integral H hm hpos hfin eta heta E hEmeas hEsub hEdis
    hEmass k C hC hstrong q hq
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hJ _) h hq0.le
  simp only [Real.rpow_eq_pow, one_div] at hh hJ
  rw [Real.rpow_inv_rpow hJ hq0.ne',
    Real.mul_rpow hcoef (Real.rpow_nonneg hA _), Real.rpow_inv_rpow hA hq0.ne'] at hh
  have hE : (∫⁻ x, (ENNReal.ofReal (finiteSetOverlap H x)) ^ q) =
      ENNReal.ofReal (∫ x, Real.rpow (finiteSetOverlap H x) q) := by
    simp_rw [ENNReal.ofReal_rpow_of_nonneg (finiteSetOverlap_nonneg H _) hq0.le]
    exact (ofReal_integral_eq_lintegral_ofReal
      (integrable_rpow_finiteSetOverlap H hm hfin q hq0)
      (Filter.Eventually.of_forall (fun x =>
        Real.rpow_nonneg (finiteSetOverlap_nonneg H x) q))).symm
  rw [hE, ENNReal.ofReal_rpow_of_nonneg hcoef hq0.le,
    ← ofReal_measureReal (volume_finiteSetShadow_lt_top H hfin).ne,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hcoef q)]
  simpa only [Real.rpow_eq_pow] using ENNReal.ofReal_le_ofReal hh

end ReyZygmund.Overlap
