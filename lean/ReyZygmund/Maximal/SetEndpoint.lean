import ReyZygmund.Maximal.SetFamily
import ReyZygmund.Maximal.EndpointStrong
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-! # Endpoint interpolation on measurable sets

The sets need only have positive finite measure; they may be unbounded. Means
remain extended-valued until finiteness is proved. This module treats bounded
tests; `SetEndpointLimit.lean` passes to increasing input limits.
-/

open MeasureTheory
open scoped ENNReal Classical

namespace ReyZygmund

theorem measurable_setFamilyMaximal {d : ℕ}
    (E : Set (Set (Fin d → ℝ))) (hE : E.Countable)
    (hmeas : ∀ I ∈ E, MeasurableSet I) (f : (Fin d → ℝ) → ℝ) :
    Measurable (setFamilyMaximal E f) := by
  have := hE.to_subtype
  exact Measurable.iSup (fun I : E =>
    measurable_const.indicator (hmeas I.1 I.2))

theorem setFamilyMaximal_mono_abs {d : ℕ}
    (E : Set (Set (Fin d → ℝ))) (f g : (Fin d → ℝ) → ℝ)
    (hfg : ∀ x, |f x| ≤ |g x|) (x : Fin d → ℝ) :
    setFamilyMaximal E f x ≤ setFamilyMaximal E g x := by
  unfold setFamilyMaximal
  apply iSup_mono
  intro I
  by_cases hx : x ∈ I.1
  · simp only [Set.indicator_of_mem hx, div_eq_mul_inv]
    exact mul_le_mul_left (lintegral_mono (fun y =>
      ENNReal.ofReal_le_ofReal (hfg y))) _
  · simp only [Set.indicator_of_notMem hx, le_refl]

theorem setFamilyMaximal_le_of_abs_le {d : ℕ}
    (E : Set (Set (Fin d → ℝ)))
    (hpos : ∀ I ∈ E, 0 < volume I) (hfin : ∀ I ∈ E, volume I < ∞)
    (f : (Fin d → ℝ) → ℝ) (B : ℝ) (_hB : 0 ≤ B)
    (hfB : ∀ x, |f x| ≤ B) (x : Fin d → ℝ) :
    setFamilyMaximal E f x ≤ ENNReal.ofReal B := by
  apply iSup_le
  intro I
  by_cases hx : x ∈ I.1
  · rw [Set.indicator_of_mem hx]
    apply (ENNReal.div_le_iff (hpos I.1 I.2).ne' (hfin I.1 I.2).ne).mpr
    calc
      _ ≤ ∫⁻ _y in I.1, ENNReal.ofReal B :=
        lintegral_mono (fun y => ENNReal.ofReal_le_ofReal (hfB y))
      _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]
  · rw [Set.indicator_of_notMem hx]
    exact zero_le

/-- Under set integrability the extended coefficient is exactly the
ordinary normalized absolute integral. -/
theorem set_lintegral_mean_eq_integral {d : ℕ}
    (I : Set (Fin d → ℝ)) (hpos : 0 < volume I) (hfin : volume I < ∞)
    (f : (Fin d → ℝ) → ℝ) (hf : IntegrableOn f I volume) :
    (∫⁻ y in I, ENNReal.ofReal |f y|) / volume I =
      ENNReal.ofReal ((∫ y in I, |f y|) / volume.real I) := by
  have hv : 0 < volume.real I := ENNReal.toReal_pos hpos.ne' hfin.ne
  rw [ENNReal.ofReal_div_of_pos hv,
    ofReal_integral_eq_lintegral_ofReal hf.abs
      (Filter.Eventually.of_forall (fun y => abs_nonneg (f y))),
    Measure.real, ENNReal.ofReal_toReal hfin.ne]

/-- The halved-level truncation works for extended means, even when
the original input is not integrable on a member of the family. -/
theorem setFamilyMaximal_truncation_levelset {d : ℕ}
    (E : Set (Set (Fin d → ℝ)))
    (hpos : ∀ I ∈ E, 0 < volume I) (hfin : ∀ I ∈ E, volume I < ∞)
    (f : (Fin d → ℝ) → ℝ) (_hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (lam : ℝ) (hlam : 0 < lam) :
    {x | ENNReal.ofReal lam < setFamilyMaximal E f x} ⊆
      {x | ENNReal.ofReal (lam / 2) < setFamilyMaximal E
        ({y | lam / 2 < f y}.indicator f) x} := by
  let g := {y | lam / 2 < f y}.indicator f
  have hg0 (y) : 0 ≤ g y := Set.indicator_nonneg (fun z _ => hf0 z) y
  have hhalf : 0 ≤ lam / 2 := by positivity
  have hpoint (y) :
      ENNReal.ofReal |f y| ≤ ENNReal.ofReal (lam / 2) + ENNReal.ofReal |g y| := by
    have hr : f y ≤ lam / 2 + g y := by
      by_cases hy : lam / 2 < f y
      · have hyS : y ∈ {z | lam / 2 < f z} := hy
        simp only [g, Set.indicator_of_mem hyS]
        linarith
      · have hyS : y ∉ {z | lam / 2 < f z} := hy
        simpa only [g, Set.indicator_of_notMem hyS, add_zero] using le_of_not_gt hy
    calc
      _ = ENNReal.ofReal (f y) := by rw [abs_of_nonneg (hf0 y)]
      _ ≤ ENNReal.ofReal (lam / 2 + g y) := ENNReal.ofReal_le_ofReal hr
      _ = _ := by rw [ENNReal.ofReal_add hhalf (hg0 y), abs_of_nonneg (hg0 y)]
  intro x hx
  change ENNReal.ofReal lam < ⨆ I : E, I.1.indicator
    (fun _ => (∫⁻ y in I.1, ENNReal.ofReal |f y|) / volume I.1) x at hx
  obtain ⟨I, hI⟩ := lt_iSup_iff.mp hx
  have hxI : x ∈ I.1 := by
    by_contra hnot
    rw [Set.indicator_of_notMem hnot] at hI
    exact (not_lt_of_ge zero_le) hI
  rw [Set.indicator_of_mem hxI] at hI
  change ENNReal.ofReal (lam / 2) < setFamilyMaximal E g x
  by_contra hnot
  have hsmall : setFamilyMaximal E g x ≤ ENNReal.ofReal (lam / 2) := le_of_not_gt hnot
  have hmean : (∫⁻ y in I.1, ENNReal.ofReal |g y|) / volume I.1 ≤
      ENNReal.ofReal (lam / 2) := by
    apply le_trans _ hsmall
    change _ ≤ ⨆ J : E, J.1.indicator
      (fun _ => (∫⁻ y in J.1, ENNReal.ofReal |g y|) / volume J.1) x
    apply le_iSup_of_le I
    rw [Set.indicator_of_mem hxI]
  have hint := (ENNReal.div_le_iff (hpos I.1 I.2).ne' (hfin I.1 I.2).ne).mp hmean
  have hhalfadd : ENNReal.ofReal (lam / 2) + ENNReal.ofReal (lam / 2) =
      ENNReal.ofReal lam := by
    rw [← ENNReal.ofReal_add hhalf hhalf]
    congr 1
    ring
  have hfull : (∫⁻ y in I.1, ENNReal.ofReal |f y|) ≤
      ENNReal.ofReal lam * volume I.1 := by
    calc
      _ ≤ ∫⁻ y in I.1, ENNReal.ofReal (lam / 2) + ENNReal.ofReal |g y| :=
        lintegral_mono hpoint
      _ = ENNReal.ofReal (lam / 2) * volume I.1 +
          ∫⁻ y in I.1, ENNReal.ofReal |g y| := by
        rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ENNReal.ofReal (lam / 2) * volume I.1 +
          ENNReal.ofReal (lam / 2) * volume I.1 := add_le_add_right hint _
      _ = _ := by rw [← add_mul, hhalfadd]
  exact (not_lt_of_ge
    ((ENNReal.div_le_iff (hpos I.1 I.2).ne' (hfin I.1 I.2).ne).mpr hfull)) hI

private theorem set_endpoint_truncated_distribution_bounded {d : ℕ}
    (H : Finset (Set (Fin d → ℝ)))
    (hpos : ∀ I ∈ H, 0 < volume I) (hfin : ∀ I ∈ H, volume I < ∞)
    (k : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweak : ∀ h : (Fin d → ℝ) → ℝ,
      Measurable h → (∀ x, 0 ≤ h x) → (∃ B : ℝ, ∀ x, h x ≤ B) →
      Bornology.IsBounded (Function.support h) → ∀ t : ℝ, 0 < t →
        volume {x | ENNReal.ofReal t < setFamilyMaximal (H : Set _) h x} ≤
          ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
            (|h x| / t * (Real.log (Real.exp 1 + |h x| / t)) ^ k))
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfB : ∃ B : ℝ, ∀ x, f x ≤ B) (hfs : Bornology.IsBounded (Function.support f))
    (lam : ℝ) (hlam : 0 < lam) :
    volume {x | ENNReal.ofReal lam < setFamilyMaximal (H : Set _) f x} ≤
      ENNReal.ofReal (2 * A / lam) *
        ∫⁻ x in {x | lam / 2 < f x}, ENNReal.ofReal
          (f x * (Real.log (Real.exp 1 + 2 * f x / lam)) ^ k) := by
  let S := {x | lam / 2 < f x}
  let g := S.indicator f
  have hS : MeasurableSet S := measurableSet_lt measurable_const hf
  have hgm : Measurable g := hf.indicator hS
  have hg0 (x) : 0 ≤ g x := Set.indicator_nonneg (fun y _ => hf0 y) x
  obtain ⟨B, hB⟩ := hfB
  have hB0 : 0 ≤ B := (hf0 0).trans (hB 0)
  have hgB (x) : g x ≤ B := by
    by_cases hx : x ∈ S
    · simpa only [g, Set.indicator_of_mem hx] using hB x
    · simpa only [g, Set.indicator_of_notMem hx] using hB0
  have hgs : Bornology.IsBounded (Function.support g) := by
    apply hfs.subset
    intro x hx
    change g x ≠ 0 at hx
    change f x ≠ 0
    intro hzero
    exact hx (by simp only [g, Set.indicator_apply, hzero, ite_self])
  have ht : 0 < lam / 2 := by positivity
  have hpoint (x) : ENNReal.ofReal
      (|g x| / (lam / 2) * (Real.log (Real.exp 1 + |g x| / (lam / 2))) ^ k) =
      ENNReal.ofReal (2 / lam) * S.indicator
        (fun y => ENNReal.ofReal
          (f y * (Real.log (Real.exp 1 + 2 * f y / lam)) ^ k)) x := by
    by_cases hx : x ∈ S
    · simp only [g, Set.indicator_of_mem hx, abs_of_nonneg (hf0 x)]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 / lam)]
      congr 1
      have hratio : f x / (lam / 2) = 2 * f x / lam := by ring
      rw [hratio]
      ring
    · simp only [g, Set.indicator_of_notMem hx, abs_zero, zero_div,
        zero_mul, ENNReal.ofReal_zero, mul_zero]
  calc
    _ ≤ volume {x | ENNReal.ofReal (lam / 2) < setFamilyMaximal (H : Set _) g x} :=
      measure_mono (setFamilyMaximal_truncation_levelset (H : Set _) hpos hfin f hf hf0 lam hlam)
    _ ≤ ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
        (|g x| / (lam / 2) * (Real.log (Real.exp 1 + |g x| / (lam / 2))) ^ k) :=
      hweak g hgm hg0 ⟨B, hgB⟩ hgs (lam / 2) ht
    _ = _ := by
      simp_rw [hpoint]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_indicator hS, ← mul_assoc, ← ENNReal.ofReal_mul hA]
      congr 2
      ring

/-- Exact strong power estimate on bounded tests. The real representative is
used only after the extended maximum is proved finite everywhere. -/
theorem finite_set_endpoint_maximal_power_bounded {d : ℕ}
    (H : Finset (Set (Fin d → ℝ))) (hmeas : ∀ I ∈ H, MeasurableSet I)
    (hpos : ∀ I ∈ H, 0 < volume I) (hfin : ∀ I ∈ H, volume I < ∞)
    (k : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hweak : ∀ h : (Fin d → ℝ) → ℝ,
      Measurable h → (∀ x, 0 ≤ h x) → (∃ B : ℝ, ∀ x, h x ≤ B) →
      Bornology.IsBounded (Function.support h) → ∀ t : ℝ, 0 < t →
        volume {x | ENNReal.ofReal t < setFamilyMaximal (H : Set _) h x} ≤
          ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
            (|h x| / t * (Real.log (Real.exp 1 + |h x| / t)) ^ k))
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfB : ∃ B : ℝ, ∀ x, f x ≤ B) (hfs : Bornology.IsBounded (Function.support f))
    (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
    (∫⁻ x, (setFamilyMaximal (H : Set _) f x) ^ p) ≤
      ENNReal.ofReal (8 * A * Real.exp 2 * (k.factorial : ℝ) /
        (p - 1) ^ (k + 1)) * ∫⁻ x, (ENNReal.ofReal |f x|) ^ p := by
  obtain ⟨B, hfB⟩ := hfB
  have hB : 0 ≤ B := (hf0 0).trans (hfB 0)
  have hMfin (x) : setFamilyMaximal (H : Set _) f x < ∞ :=
    (setFamilyMaximal_le_of_abs_le (H : Set _) hpos hfin f B hB
      (fun y => by simpa only [abs_of_nonneg (hf0 y)] using hfB y) x).trans_lt
        ENNReal.ofReal_lt_top
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hstrong :
      (∫⁻ x, ENNReal.ofReal ((setFamilyMaximal (H : Set _) f x).toReal ^ p)) ≤
        ENNReal.ofReal (8 * A * Real.exp 2 * (k.factorial : ℝ) /
          (p - 1) ^ (k + 1)) * ∫⁻ x, ENNReal.ofReal (f x ^ p) := by
    apply endpoint_distribution_strong_power volume f
      (fun x => (setFamilyMaximal (H : Set _) f x).toReal) hf hf0
      (measurable_setFamilyMaximal (H : Set _) H.countable_toSet hmeas f).ennreal_toReal
      (fun _ => ENNReal.toReal_nonneg) k p A hp hp2 hA
    intro t ht
    have hsets : {x | t < (setFamilyMaximal (H : Set _) f x).toReal} =
        {x | ENNReal.ofReal t < setFamilyMaximal (H : Set _) f x} := by
      ext x
      change (t < (setFamilyMaximal (H : Set _) f x).toReal) ↔
        ENNReal.ofReal t < setFamilyMaximal (H : Set _) f x
      calc
        _ ↔ ENNReal.ofReal t < ENNReal.ofReal
            (setFamilyMaximal (H : Set _) f x).toReal :=
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).symm
        _ ↔ _ := by rw [ENNReal.ofReal_toReal (hMfin x).ne]
    rw [hsets]
    exact set_endpoint_truncated_distribution_bounded H hpos hfin k A hA hweak
      f hf hf0 ⟨B, hfB⟩ hfs t ht
  have houtput (x) : ENNReal.ofReal ((setFamilyMaximal (H : Set _) f x).toReal ^ p) =
      (setFamilyMaximal (H : Set _) f x) ^ p := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp0.le,
      ENNReal.ofReal_toReal (hMfin x).ne]
  have hinput (x) : ENNReal.ofReal (f x ^ p) = (ENNReal.ofReal |f x|) ^ p := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (hf0 x) hp0.le, abs_of_nonneg (hf0 x)]
  simpa only [houtput, hinput] using hstrong

end ReyZygmund
