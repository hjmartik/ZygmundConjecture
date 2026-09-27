import ReyZygmund.Overlap.SetFinite
import ReyZygmund.Maximal.SetEndpoint
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Sparse pairing on arbitrary finite measurable-set families

Memberwise integrability identifies the extended means with real
means. A finite indicator-sum majorant supplies finiteness and integrability
without any spatial boundedness assumption on the sets.
-/

open MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Overlap

variable {d : ℕ}

private theorem finiteSetMaximal_le_mean_sum
    (H : Finset (Set (Fin d → ℝ)))
    (hpos : ∀ I ∈ H, 0 < volume I) (hfin : ∀ I ∈ H, volume I < ∞)
    (f : (Fin d → ℝ) → ℝ) (hfi : ∀ I ∈ H, IntegrableOn f I volume)
    (x : Fin d → ℝ) :
    setFamilyMaximal (H : Set _) f x ≤ ENNReal.ofReal
      (∑ I ∈ H, I.indicator (fun _ => (∫ y in I, |f y|) / volume.real I) x) := by
  apply iSup_le
  intro I
  by_cases hx : x ∈ I.1
  · rw [Set.indicator_of_mem hx,
      set_lintegral_mean_eq_integral I.1 (hpos I.1 I.2) (hfin I.1 I.2) f (hfi I.1 I.2)]
    apply ENNReal.ofReal_le_ofReal
    have h := Finset.single_le_sum (f := fun J : Set (Fin d → ℝ) =>
        J.indicator (fun _ => (∫ y in J, |f y|) / volume.real J) x)
      (fun J _ => Set.indicator_nonneg
        (fun _ _ => div_nonneg (integral_nonneg (fun _ => abs_nonneg _))
          measureReal_nonneg) x) I.2
    simpa only [Set.indicator_of_mem hx] using h
  · rw [Set.indicator_of_notMem hx]
    exact zero_le

/-- Memberwise integrability makes the finite maximum finite
at every point, before its real representative is used. -/
theorem setFamilyMaximal_finset_lt_top
    (H : Finset (Set (Fin d → ℝ)))
    (hpos : ∀ I ∈ H, 0 < volume I) (hfin : ∀ I ∈ H, volume I < ∞)
    (f : (Fin d → ℝ) → ℝ) (hfi : ∀ I ∈ H, IntegrableOn f I volume)
    (x : Fin d → ℝ) : setFamilyMaximal (H : Set _) f x < ∞ :=
  lt_of_le_of_lt (finiteSetMaximal_le_mean_sum H hpos hfin f hfi x)
    ENNReal.ofReal_lt_top

/-- A finite sum of supported means is an Lp majorant for every
exponent, including infinity. The member sets need not be bounded. -/
theorem memLp_setFamilyMaximal_finset
    (H : Finset (Set (Fin d → ℝ))) (hm : ∀ I ∈ H, MeasurableSet I)
    (hpos : ∀ I ∈ H, 0 < volume I) (hfin : ∀ I ∈ H, volume I < ∞)
    (f : (Fin d → ℝ) → ℝ) (hfi : ∀ I ∈ H, IntegrableOn f I volume)
    (p : ℝ≥0∞) :
    MemLp (fun x => (setFamilyMaximal (H : Set _) f x).toReal) p volume := by
  let b : (Fin d → ℝ) → ℝ := fun x =>
    ∑ I ∈ H, I.indicator (fun _ => (∫ y in I, |f y|) / volume.real I) x
  have hb0 (x) : 0 ≤ b x := Finset.sum_nonneg (fun I _ =>
    Set.indicator_nonneg (fun _ _ =>
      div_nonneg (integral_nonneg (fun _ => abs_nonneg _)) measureReal_nonneg) x)
  have hb : MemLp b p volume := by
    apply memLp_finsetSum
    intro I hI
    exact memLp_indicator_const p (hm I hI) _ (Or.inr (hfin I hI).ne)
  have hmeas := (measurable_setFamilyMaximal (H : Set _) H.countable_toSet hm f).ennreal_toReal
  apply hb.mono' hmeas.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (finiteSetMaximal_le_mean_sum H hpos hfin f hfi x)
  exact h.trans_eq (ENNReal.toReal_ofReal (hb0 x))

private theorem pairing_integrable_and_integral
    (H : Finset (Set (Fin d → ℝ))) (hm : ∀ I ∈ H, MeasurableSet I)
    (g : (Fin d → ℝ) → ℝ) (hgi : ∀ I ∈ H, IntegrableOn g I volume) :
    Integrable (fun x => finiteSetOverlap H x * g x) volume ∧
      (∫ x, finiteSetOverlap H x * g x) = ∑ I ∈ H, ∫ x in I, g x := by
  have heq : (fun x => finiteSetOverlap H x * g x) =
      (fun x => ∑ I ∈ H, I.indicator g x) := by
    funext x
    rw [finiteSetOverlap, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro I _
    by_cases hx : x ∈ I
    · simp only [Set.indicator_of_mem hx, one_mul]
    · simp only [Set.indicator_of_notMem hx, zero_mul]
  have hi (I) (hI : I ∈ H) : Integrable (I.indicator g) volume :=
    (hgi I hI).integrable_indicator (hm I hI)
  constructor
  · rw [heq]
    exact integrable_finsetSum H hi
  · rw [heq, integral_finsetSum H hi]
    exact Finset.sum_congr rfl (fun I hI => integral_indicator (hm I hI))

private theorem absolute_mean_le_finiteSetMaximal
    (H : Finset (Set (Fin d → ℝ)))
    (hpos : ∀ I ∈ H, 0 < volume I) (hfin : ∀ I ∈ H, volume I < ∞)
    (g : (Fin d → ℝ) → ℝ) (hgi : ∀ I ∈ H, IntegrableOn g I volume)
    (I : Set (Fin d → ℝ)) (hI : I ∈ H) (x : Fin d → ℝ) (hx : x ∈ I) :
    (∫ y in I, |g y|) / volume.real I ≤
      (setFamilyMaximal (H : Set _) g x).toReal := by
  have hmean : 0 ≤ (∫ y in I, |g y|) / volume.real I :=
    div_nonneg (integral_nonneg (fun _ => abs_nonneg _)) measureReal_nonneg
  have hsup : ENNReal.ofReal ((∫ y in I, |g y|) / volume.real I) ≤
      setFamilyMaximal (H : Set _) g x := by
    rw [← set_lintegral_mean_eq_integral I (hpos I hI) (hfin I hI) g (hgi I hI)]
    apply le_iSup_of_le (⟨I, hI⟩ : (H : Set _))
    rw [Set.indicator_of_mem hx]
  simpa only [ENNReal.toReal_ofReal hmean] using
    ENNReal.toReal_mono (setFamilyMaximal_finset_lt_top H hpos hfin g hgi x).ne hsup

/-- Disjoint measurable subsets give the sparse pairing estimate for sets of positive
finite measure. Values outside the shadow are unrestricted. -/
theorem finite_set_sparse_pairing
    (H : Finset (Set (Fin d → ℝ))) (hm : ∀ I ∈ H, MeasurableSet I)
    (hpos : ∀ I ∈ H, 0 < volume I) (hfin : ∀ I ∈ H, volume I < ∞)
    (eta : ℝ) (heta : 0 < eta)
    (E : Set (Fin d → ℝ) → Set (Fin d → ℝ))
    (hEmeas : ∀ I ∈ H, MeasurableSet (E I)) (hEsub : ∀ I ∈ H, E I ⊆ I)
    (hEdis : Set.Pairwise (H : Set (Set (Fin d → ℝ)))
      (fun I J => Disjoint (E I) (E J)))
    (hEmass : ∀ I ∈ H, ENNReal.ofReal eta * volume I ≤ volume (E I))
    (g : (Fin d → ℝ) → ℝ) (hg0 : ∀ x ∈ finiteSetShadow H, 0 ≤ g x)
    (hgi : ∀ I ∈ H, IntegrableOn g I volume) :
    eta * (∫ x, finiteSetOverlap H x * g x) ≤
      ∫ x in finiteSetShadow H, (setFamilyMaximal (H : Set _) g x).toReal := by
  obtain ⟨_, hpair⟩ := pairing_integrable_and_integral H hm g hgi
  have hM : Integrable (fun x => (setFamilyMaximal (H : Set _) g x).toReal) volume :=
    memLp_one_iff_integrable.mp (memLp_setFamilyMaximal_finset H hm hpos hfin g hgi 1)
  have hterm (I) (hI : I ∈ H) :
      eta * (∫ x in I, g x) ≤ ∫ x in E I, (setFamilyMaximal (H : Set _) g x).toReal := by
    have hEfinite : volume (E I) < ∞ :=
      lt_of_le_of_lt (measure_mono (hEsub I hI)) (hfin I hI)
    have hmass : eta * volume.real I ≤ volume.real (E I) := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal heta.le, measureReal_def] using
        ENNReal.toReal_mono hEfinite.ne (hEmass I hI)
    have hvol : 0 < volume.real I :=
      ENNReal.toReal_pos (hpos I hI).ne' (hfin I hI).ne
    have hnonneg : ∀ x ∈ I, 0 ≤ g x :=
      fun x hx => hg0 x (subset_finiteSetShadow H I hI hx)
    have habs : (∫ x in I, |g x|) = ∫ x in I, g x :=
      setIntegral_congr_fun (hm I hI) (fun x hx => abs_of_nonneg (hnonneg x hx))
    have hmean : 0 ≤ (∫ x in I, g x) / volume.real I :=
      div_nonneg (setIntegral_nonneg (hm I hI) hnonneg) hvol.le
    have hpoint (x) (hx : x ∈ E I) :
        (∫ y in I, g y) / volume.real I ≤
          (setFamilyMaximal (H : Set _) g x).toReal := by
      rw [← habs]
      exact absolute_mean_le_finiteSetMaximal H hpos hfin g hgi I hI x (hEsub I hI hx)
    calc
      _ = (eta * volume.real I) * ((∫ x in I, g x) / volume.real I) := by
        rw [mul_assoc, mul_comm (volume.real I) _, div_mul_cancel₀ _ hvol.ne']
      _ ≤ volume.real (E I) * ((∫ x in I, g x) / volume.real I) :=
        mul_le_mul_of_nonneg_right hmass hmean
      _ ≤ _ := by
        simpa only [smul_eq_mul] using
          setIntegral_ge_of_const_le (hEmeas I hI) hEfinite.ne hpoint hM.integrableOn
  have hsub : (⋃ I ∈ H, E I) ⊆ finiteSetShadow H :=
    Set.iUnion_subset (fun I => Set.iUnion_subset (fun hI =>
      (hEsub I hI).trans (subset_finiteSetShadow H I hI)))
  calc
    _ = ∑ I ∈ H, eta * (∫ x in I, g x) := by rw [hpair, Finset.mul_sum]
    _ ≤ ∑ I ∈ H, ∫ x in E I, (setFamilyMaximal (H : Set _) g x).toReal :=
      Finset.sum_le_sum hterm
    _ = ∫ x in ⋃ I ∈ H, E I, (setFamilyMaximal (H : Set _) g x).toReal :=
      (integral_biUnion_finset H hEmeas hEdis (fun _ _ => hM.integrableOn)).symm
    _ ≤ _ := setIntegral_mono_set hM.integrableOn
      (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
      (Filter.Eventually.of_forall (fun _ hx => hsub hx))

end ReyZygmund.Overlap
