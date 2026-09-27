import ReyZygmund.Maximal.SetEndpoint
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! # Increasing bounded tests recover the measurable-set maximum

Both the averages and the final power integral remain extended nonnegative
integrals. No finite integral is assigned to an arbitrary measurable input.
-/

open Filter MeasureTheory
open scoped ENNReal Classical Topology

namespace ReyZygmund

private noncomputable def setEndpointCutoff {d : ℕ}
    (f : (Fin d → ℝ) → ℝ) (n : ℕ) : (Fin d → ℝ) → ℝ :=
  (Metric.closedBall 0 (n : ℝ)).indicator (fun x => min |f x| (n : ℝ))

private theorem setEndpointCutoff_measurable {d : ℕ}
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (n : ℕ) :
    Measurable (setEndpointCutoff f n) := by
  have ha : Measurable (fun x => |f x|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  exact (ha.min measurable_const).indicator measurableSet_closedBall

private theorem setEndpointCutoff_nonneg {d : ℕ}
    (f : (Fin d → ℝ) → ℝ) (n : ℕ) (x : Fin d → ℝ) :
    0 ≤ setEndpointCutoff f n x :=
  Set.indicator_nonneg (fun y _ => le_min (abs_nonneg (f y)) (Nat.cast_nonneg n)) x

private theorem setEndpointCutoff_le_abs {d : ℕ}
    (f : (Fin d → ℝ) → ℝ) (n : ℕ) (x : Fin d → ℝ) :
    setEndpointCutoff f n x ≤ |f x| := by
  by_cases hx : x ∈ Metric.closedBall 0 (n : ℝ)
  · simpa only [setEndpointCutoff, Set.indicator_of_mem hx] using min_le_left |f x| (n : ℝ)
  · simpa only [setEndpointCutoff, Set.indicator_of_notMem hx] using abs_nonneg (f x)

private theorem setEndpointCutoff_le_height {d : ℕ}
    (f : (Fin d → ℝ) → ℝ) (n : ℕ) (x : Fin d → ℝ) :
    setEndpointCutoff f n x ≤ (n : ℝ) := by
  by_cases hx : x ∈ Metric.closedBall 0 (n : ℝ)
  · simpa only [setEndpointCutoff, Set.indicator_of_mem hx] using min_le_right |f x| (n : ℝ)
  · simpa only [setEndpointCutoff, Set.indicator_of_notMem hx] using Nat.cast_nonneg (α := ℝ) n

private theorem setEndpointCutoff_bounded_support {d : ℕ}
    (f : (Fin d → ℝ) → ℝ) (n : ℕ) :
    Bornology.IsBounded (Function.support (setEndpointCutoff f n)) := by
  have hball : Bornology.IsBounded (Metric.closedBall (0 : Fin d → ℝ) (n : ℝ)) :=
    Metric.isBounded_closedBall
  apply hball.subset
  intro x hx
  change setEndpointCutoff f n x ≠ 0 at hx
  by_contra hnot
  exact hx (by simp only [setEndpointCutoff, Set.indicator_of_notMem hnot])

private theorem setEndpointCutoff_mono {d : ℕ}
    (f : (Fin d → ℝ) → ℝ) : Monotone (setEndpointCutoff f) := by
  intro n l hnl x
  by_cases hx : x ∈ Metric.closedBall 0 (n : ℝ)
  · have hxl : x ∈ Metric.closedBall 0 (l : ℝ) :=
      Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hnl) hx
    simp only [setEndpointCutoff, Set.indicator_of_mem hx, Set.indicator_of_mem hxl]
    exact min_le_min le_rfl (Nat.cast_le.mpr hnl)
  · rw [setEndpointCutoff, Set.indicator_of_notMem hx]
    exact setEndpointCutoff_nonneg f l x

private theorem ofReal_abs_eq_iSup_cutoff {d : ℕ}
    (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    ENNReal.ofReal |f x| = ⨆ n : ℕ, ENNReal.ofReal (setEndpointCutoff f n x) := by
  apply le_antisymm
  · obtain ⟨n, hn⟩ := exists_nat_ge (max ‖x‖ |f x|)
    have hx : x ∈ Metric.closedBall 0 (n : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using (le_max_left _ _).trans hn
    have hf : |f x| ≤ (n : ℝ) := (le_max_right _ _).trans hn
    apply le_iSup_of_le n
    simp only [setEndpointCutoff, Set.indicator_of_mem hx, min_eq_left hf, le_refl]
  · exact iSup_le (fun n => ENNReal.ofReal_le_ofReal (setEndpointCutoff_le_abs f n x))

private theorem setFamilyMaximal_eq_iSup_cutoff {d : ℕ}
    (E : Set (Set (Fin d → ℝ))) (f : (Fin d → ℝ) → ℝ) (hf : Measurable f)
    (x : Fin d → ℝ) :
    setFamilyMaximal E f x = ⨆ n : ℕ, setFamilyMaximal E (setEndpointCutoff f n) x := by
  have hmean (I : Set (Fin d → ℝ)) :
      (∫⁻ y in I, ENNReal.ofReal |f y|) / volume I =
        ⨆ n : ℕ, (∫⁻ y in I, ENNReal.ofReal (setEndpointCutoff f n y)) / volume I := by
    calc
      _ = (∫⁻ y in I, ⨆ n : ℕ, ENNReal.ofReal (setEndpointCutoff f n y)) / volume I :=
        congrArg (fun z : ℝ≥0∞ => z / volume I)
          (lintegral_congr (ofReal_abs_eq_iSup_cutoff f))
      _ = _ := by
        rw [lintegral_iSup
          (fun n => (setEndpointCutoff_measurable f hf n).ennreal_ofReal)
          (fun n l hnl y => ENNReal.ofReal_le_ofReal (setEndpointCutoff_mono f hnl y)),
          ENNReal.iSup_div]
  calc
    _ = ⨆ I : E, ⨆ n : ℕ, I.1.indicator
        (fun _ => (∫⁻ y in I.1, ENNReal.ofReal (setEndpointCutoff f n y)) / volume I.1) x := by
      apply iSup_congr
      intro I
      by_cases hx : x ∈ I.1
      · simp only [Set.indicator_of_mem hx]
        exact hmean I.1
      · simp only [Set.indicator_of_notMem hx, iSup_const]
    _ = ⨆ n : ℕ, ⨆ I : E, I.1.indicator
        (fun _ => (∫⁻ y in I.1, ENNReal.ofReal (setEndpointCutoff f n y)) / volume I.1) x :=
      iSup_comm
    _ = _ := by
      apply iSup_congr
      intro n
      apply iSup_congr
      intro I
      simp only [abs_of_nonneg (setEndpointCutoff_nonneg f n _)]

/-- The bounded-test endpoint hypothesis gives the exact strong power bound
for every measurable signed input, with all infinite values retained. -/
theorem finite_set_endpoint_maximal_power {d : ℕ}
    (H : Finset (Set (Fin d → ℝ))) (hmeas : ∀ I ∈ H, MeasurableSet I)
    (hpos : ∀ I ∈ H, 0 < volume I) (hfin : ∀ I ∈ H, volume I < ∞)
    (k : ℕ) (A : ℝ) (hA : 1 ≤ A)
    (hweak : ∀ h : (Fin d → ℝ) → ℝ,
      Measurable h → (∀ x, 0 ≤ h x) → (∃ B : ℝ, ∀ x, h x ≤ B) →
      Bornology.IsBounded (Function.support h) → ∀ t : ℝ, 0 < t →
        volume {x | ENNReal.ofReal t < setFamilyMaximal (H : Set _) h x} ≤
          ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
            (|h x| / t * (Real.log (Real.exp 1 + |h x| / t)) ^ k))
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f)
    (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
    (∫⁻ x, (setFamilyMaximal (H : Set _) f x) ^ p) ≤
      ENNReal.ofReal (8 * A * Real.exp 2 * (k.factorial : ℝ) /
        (p - 1) ^ (k + 1)) * ∫⁻ x, (ENNReal.ofReal |f x|) ^ p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hA0 : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans hA
  let F (n : ℕ) (x : Fin d → ℝ) : ℝ≥0∞ :=
    (setFamilyMaximal (H : Set _) (setEndpointCutoff f n) x) ^ p
  have hFm (n : ℕ) : Measurable (F n) :=
    (measurable_setFamilyMaximal (H : Set _) H.countable_toSet hmeas
      (setEndpointCutoff f n)).pow_const p
  have hFmono : Monotone F := by
    intro n l hnl x
    apply ENNReal.rpow_le_rpow _ hp0.le
    apply setFamilyMaximal_mono_abs
    intro y
    rw [abs_of_nonneg (setEndpointCutoff_nonneg f n y),
      abs_of_nonneg (setEndpointCutoff_nonneg f l y)]
    exact setEndpointCutoff_mono f hnl y
  have heq (x : Fin d → ℝ) :
      (setFamilyMaximal (H : Set _) f x) ^ p = ⨆ n : ℕ, F n x := by
    rw [setFamilyMaximal_eq_iSup_cutoff (H : Set _) f hf x]
    exact (ENNReal.orderIsoRpow p hp0).map_iSup
      (fun n : ℕ => setFamilyMaximal (H : Set _) (setEndpointCutoff f n) x)
  calc
    _ = ∫⁻ x, ⨆ n : ℕ, F n x := lintegral_congr heq
    _ = ⨆ n : ℕ, ∫⁻ x, F n x := lintegral_iSup hFm hFmono
    _ ≤ _ := by
      apply iSup_le
      intro n
      refine (finite_set_endpoint_maximal_power_bounded H hmeas hpos hfin k A hA0 hweak
        (setEndpointCutoff f n) (setEndpointCutoff_measurable f hf n)
        (setEndpointCutoff_nonneg f n) ⟨(n : ℝ), setEndpointCutoff_le_height f n⟩
        (setEndpointCutoff_bounded_support f n) p hp hp2).trans ?_
      apply mul_le_mul_right
      apply lintegral_mono
      intro x
      apply ENNReal.rpow_le_rpow _ hp0.le
      apply ENNReal.ofReal_le_ofReal
      rw [abs_of_nonneg (setEndpointCutoff_nonneg f n x)]
      exact setEndpointCutoff_le_abs f n x

end ReyZygmund
