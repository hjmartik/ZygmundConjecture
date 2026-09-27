import ReyZygmund.Maximal.Euclidean
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.MetricSpace.Bounded

/-! # Extending the finite endpoint inequality from bounded tests

Height and spatial truncations recover each rectangle average. The
extended logarithmic integral need not be finite. A measurable representative
then gives the signed locally integrable formulation needed by interpolation.
-/

open BoxIntegral Filter MeasureTheory
open scoped BigOperators Classical ENNReal Topology

namespace ReyZygmund

open Geometry

private noncomputable def boundedTestCutoff {q : ℕ}
    (g : (Fin q → ℝ) → ℝ) (n : ℕ) : (Fin q → ℝ) → ℝ :=
  (Metric.closedBall 0 (n : ℝ)).indicator (fun x => min (g x) (n : ℝ))

private theorem boundedTestCutoff_measurable {q : ℕ}
    (g : (Fin q → ℝ) → ℝ) (hg : Measurable g) (n : ℕ) :
    Measurable (boundedTestCutoff g n) :=
  (hg.min measurable_const).indicator measurableSet_closedBall

private theorem boundedTestCutoff_nonneg {q : ℕ}
    (g : (Fin q → ℝ) → ℝ) (hg : ∀ x, 0 ≤ g x) (n : ℕ) (x : Fin q → ℝ) :
    0 ≤ boundedTestCutoff g n x :=
  Set.indicator_nonneg (fun y _ => le_min (hg y) (Nat.cast_nonneg n)) x

private theorem boundedTestCutoff_le {q : ℕ}
    (g : (Fin q → ℝ) → ℝ) (hg : ∀ x, 0 ≤ g x) (n : ℕ) (x : Fin q → ℝ) :
    boundedTestCutoff g n x ≤ g x := by
  by_cases hx : x ∈ Metric.closedBall 0 (n : ℝ)
  · simpa only [boundedTestCutoff, Set.indicator_of_mem hx] using min_le_left (g x) (n : ℝ)
  · simpa only [boundedTestCutoff, Set.indicator_of_notMem hx] using hg x

private theorem boundedTestCutoff_le_height {q : ℕ}
    (g : (Fin q → ℝ) → ℝ) (n : ℕ) (x : Fin q → ℝ) :
    boundedTestCutoff g n x ≤ (n : ℝ) := by
  by_cases hx : x ∈ Metric.closedBall 0 (n : ℝ)
  · simpa only [boundedTestCutoff, Set.indicator_of_mem hx] using min_le_right (g x) (n : ℝ)
  · simpa only [boundedTestCutoff, Set.indicator_of_notMem hx] using Nat.cast_nonneg (α := ℝ) n

private theorem boundedTestCutoff_bounded_support {q : ℕ}
    (g : (Fin q → ℝ) → ℝ) (n : ℕ) :
    Bornology.IsBounded (Function.support (boundedTestCutoff g n)) := by
  have hball : Bornology.IsBounded (Metric.closedBall (0 : Fin q → ℝ) (n : ℝ)) :=
    Metric.isBounded_closedBall
  apply hball.subset
  intro x hx
  change boundedTestCutoff g n x ≠ 0 at hx
  by_contra hnot
  exact hx (by simp only [boundedTestCutoff, Set.indicator_of_notMem hnot])

private theorem boundedTestCutoff_mono {q : ℕ}
    (g : (Fin q → ℝ) → ℝ) (hg : ∀ x, 0 ≤ g x) :
    Monotone (boundedTestCutoff g) := by
  intro n l hnl x
  by_cases hx : x ∈ Metric.closedBall 0 (n : ℝ)
  · have hxl : x ∈ Metric.closedBall 0 (l : ℝ) :=
      Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hnl) hx
    simp only [boundedTestCutoff, Set.indicator_of_mem hx, Set.indicator_of_mem hxl]
    exact min_le_min le_rfl (Nat.cast_le.mpr hnl)
  · rw [boundedTestCutoff, Set.indicator_of_notMem hx]
    exact boundedTestCutoff_nonneg g hg l x

private theorem boundedTestCutoff_tendsto {q : ℕ}
    (g : (Fin q → ℝ) → ℝ) (x : Fin q → ℝ) :
    Tendsto (fun n => boundedTestCutoff g n x) atTop (𝓝 (g x)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max ‖x‖ (g x))
  have heq : (fun n => boundedTestCutoff g n x) =ᶠ[atTop] fun _ => g x := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hxn : ‖x‖ ≤ (n : ℝ) :=
      (le_max_left _ _).trans (hN.trans (Nat.cast_le.mpr hn))
    have hgn : g x ≤ (n : ℝ) :=
      (le_max_right _ _).trans (hN.trans (Nat.cast_le.mpr hn))
    have hx : x ∈ Metric.closedBall 0 (n : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hxn
    simp only [boundedTestCutoff, Set.indicator_of_mem hx, min_eq_left hgn]
  exact tendsto_const_nhds.congr' heq.symm

private theorem boundedTestCutoff_locallyIntegrable {q : ℕ}
    (g : (Fin q → ℝ) → ℝ) (hg : LocallyIntegrable g volume)
    (hm : Measurable g) (hn : ∀ x, 0 ≤ g x) (n : ℕ) :
    LocallyIntegrable (boundedTestCutoff g n) volume := by
  apply hg.mono (boundedTestCutoff_measurable g hm n).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (boundedTestCutoff_nonneg g hn n x),
      abs_of_nonneg (hn x)] using boundedTestCutoff_le g hn n x

private theorem nonnegative_box_average_mono {q : ℕ}
    (Q : Box (Fin q)) (f g : (Fin q → ℝ) → ℝ)
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hfg : ∀ x, f x ≤ g x) :
    (∫ x in (Q : Set (Fin q → ℝ)), |f x|) / volume.real (Q : Set (Fin q → ℝ)) ≤
      (∫ x in (Q : Set (Fin q → ℝ)), |g x|) / volume.real (Q : Set (Fin q → ℝ)) := by
  have hfi := (hf.integrableOn_isCompact Q.isCompact_Icc).mono_set Box.coe_subset_Icc
  have hgi := (hg.integrableOn_isCompact Q.isCompact_Icc).mono_set Box.coe_subset_Icc
  have hi := integral_mono hfi hgi hfg
  simpa only [abs_of_nonneg (hf0 _), abs_of_nonneg (hg0 _)] using
    div_le_div_of_nonneg_right hi (box_volume_pos Q).le

private theorem boundedTestCutoff_average_tendsto {q : ℕ}
    (Q : Box (Fin q)) (g : (Fin q → ℝ) → ℝ) (hg : LocallyIntegrable g volume)
    (hm : Measurable g) (hn : ∀ x, 0 ≤ g x) :
    Tendsto (fun n =>
      (∫ x in (Q : Set (Fin q → ℝ)), |boundedTestCutoff g n x|) /
        volume.real (Q : Set (Fin q → ℝ))) atTop
      (𝓝 ((∫ x in (Q : Set (Fin q → ℝ)), |g x|) /
        volume.real (Q : Set (Fin q → ℝ)))) := by
  have hgi : Integrable g (volume.restrict (Q : Set (Fin q → ℝ))) :=
    (hg.integrableOn_isCompact Q.isCompact_Icc).mono_set Box.coe_subset_Icc
  have hi := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Q : Set (Fin q → ℝ))) g
    (fun n => (boundedTestCutoff_measurable g hm n).aestronglyMeasurable) hgi
    (fun n => Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (boundedTestCutoff_nonneg g hn n x)]
        using boundedTestCutoff_le g hn n x)
    (Eventually.of_forall (boundedTestCutoff_tendsto g))
  simpa only [abs_of_nonneg (boundedTestCutoff_nonneg g hn _ _),
    abs_of_nonneg (hn _)] using hi.div_const (volume.real (Q : Set (Fin q → ℝ)))

private theorem nonnegative_maximal_mono
    {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i))))
    (f g : (Fin (∑ i, d i) → ℝ) → ℝ)
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hfg : ∀ x, f x ≤ g x)
    (x : Fin (∑ i, d i) → ℝ) :
    euclideanFamilyMaximal G f x ≤ euclideanFamilyMaximal G g x := by
  unfold euclideanFamilyMaximal
  apply iSup_mono
  intro Q
  apply ENNReal.ofReal_le_ofReal
  by_cases hx : x ∈ (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ))
  · simp only [Set.indicator_of_mem hx]
    exact nonnegative_box_average_mono (flatProductBox Q.1) f g hf hg hf0 hg0 hfg
  · simp only [Set.indicator_of_notMem hx, le_refl]

private theorem boundedTestCutoff_levelset
    {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i))))
    (g : (Fin (∑ i, d i) → ℝ) → ℝ) (hg : LocallyIntegrable g volume)
    (hm : Measurable g) (hn : ∀ x, 0 ≤ g x) (t : ℝ) (ht : 0 < t) :
    {x | ENNReal.ofReal t < euclideanFamilyMaximal G g x} =
      ⋃ n : ℕ, {x | ENNReal.ofReal t <
        euclideanFamilyMaximal G (boundedTestCutoff g n) x} := by
  ext x
  constructor
  · intro hx
    change ENNReal.ofReal t < ⨆ Q : G, ENNReal.ofReal
      ((flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)).indicator
        (fun _ => (∫ y in (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)), |g y|) /
          volume.real (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ))) x) at hx
    obtain ⟨Q, hQ⟩ := lt_iSup_iff.mp hx
    have hxQ : x ∈ (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)) := by
      by_contra hnot
      simp only [Set.indicator_of_notMem hnot, ENNReal.ofReal_zero] at hQ
      exact (not_lt_of_ge zero_le) hQ
    rw [Set.indicator_of_mem hxQ] at hQ
    have hstrict := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mp hQ
    have hlim := boundedTestCutoff_average_tendsto (flatProductBox Q.1) g hg hm hn
    obtain ⟨n, hnt⟩ := (hlim.eventually (eventually_gt_nhds hstrict)).exists
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change ENNReal.ofReal t < ⨆ Q : G, ENNReal.ofReal
      ((flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)).indicator
        (fun _ => (∫ y in (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)),
          |boundedTestCutoff g n y|) /
          volume.real (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ))) x)
    apply lt_of_lt_of_le _ (le_iSup_of_le Q le_rfl)
    rw [Set.indicator_of_mem hxQ]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mpr hnt
  · intro hx
    obtain ⟨n, hnt⟩ := Set.mem_iUnion.mp hx
    exact lt_of_lt_of_le hnt (nonnegative_maximal_mono G (boundedTestCutoff g n) g
      (boundedTestCutoff_locallyIntegrable g hg hm hn n) hg
      (boundedTestCutoff_nonneg g hn n) hn (boundedTestCutoff_le g hn n) x)

private theorem endpoint_integrand_mono (k : ℕ) (t : ℝ) (ht : 0 < t)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a / t * (Real.log (Real.exp 1 + a / t)) ^ k ≤
      b / t * (Real.log (Real.exp 1 + b / t)) ^ k := by
  have hdiv : a / t ≤ b / t := div_le_div_of_nonneg_right hab ht.le
  have hdiv0 : 0 ≤ a / t := div_nonneg ha ht.le
  have hexp : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr zero_le_one
  have hlog0 : 0 ≤ Real.log (Real.exp 1 + a / t) :=
    Real.log_nonneg (hexp.trans (le_add_of_nonneg_right hdiv0))
  have hlog : Real.log (Real.exp 1 + a / t) ≤ Real.log (Real.exp 1 + b / t) :=
    Real.log_le_log ((Real.exp_pos 1).trans_le (le_add_of_nonneg_right hdiv0))
      (add_le_add le_rfl hdiv)
  exact mul_le_mul hdiv (pow_le_pow_left₀ hlog0 hlog k)
    (pow_nonneg hlog0 k) (hdiv0.trans hdiv)

private theorem bounded_endpoint_nonnegative
    {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i))))
    (k : ℕ) (A : ℝ)
    (hweak : ∀ h : (Fin (∑ i, d i) → ℝ) → ℝ,
      Measurable h → (∀ x, 0 ≤ h x) → (∃ B : ℝ, ∀ x, h x ≤ B) →
      Bornology.IsBounded (Function.support h) → ∀ t : ℝ, 0 < t →
      volume {x | ENNReal.ofReal t < euclideanFamilyMaximal (G : Set _) h x} ≤
        ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
          (|h x| / t * (Real.log (Real.exp 1 + |h x| / t)) ^ k))
    (g : (Fin (∑ i, d i) → ℝ) → ℝ) (hg : LocallyIntegrable g volume)
    (hm : Measurable g) (hn : ∀ x, 0 ≤ g x) (t : ℝ) (ht : 0 < t) :
    volume {x | ENNReal.ofReal t < euclideanFamilyMaximal (G : Set _) g x} ≤
      ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
        (|g x| / t * (Real.log (Real.exp 1 + |g x| / t)) ^ k) := by
  have hsets : Monotone (fun n : ℕ => {x | ENNReal.ofReal t <
      euclideanFamilyMaximal (G : Set _) (boundedTestCutoff g n) x}) := by
    intro n l hnl x hx
    exact lt_of_lt_of_le hx
      (nonnegative_maximal_mono (G : Set _) (boundedTestCutoff g n) (boundedTestCutoff g l)
        (boundedTestCutoff_locallyIntegrable g hg hm hn n)
        (boundedTestCutoff_locallyIntegrable g hg hm hn l)
        (boundedTestCutoff_nonneg g hn n) (boundedTestCutoff_nonneg g hn l)
        (boundedTestCutoff_mono g hn hnl) x)
  rw [boundedTestCutoff_levelset (G : Set _) g hg hm hn t ht, hsets.measure_iUnion]
  apply iSup_le
  intro n
  refine (hweak (boundedTestCutoff g n) (boundedTestCutoff_measurable g hm n)
    (boundedTestCutoff_nonneg g hn n)
    ⟨(n : ℝ), boundedTestCutoff_le_height g n⟩
    (boundedTestCutoff_bounded_support g n) t ht).trans ?_
  apply mul_le_mul_right
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  simpa only [abs_of_nonneg (boundedTestCutoff_nonneg g hn n x), abs_of_nonneg (hn x)] using
    endpoint_integrand_mono k t ht (boundedTestCutoff_nonneg g hn n x)
      (boundedTestCutoff_le g hn n x)

private theorem maximal_congr_abs_ae
    {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i))))
    (f g : (Fin (∑ i, d i) → ℝ) → ℝ)
    (hfg : (fun x => |f x|) =ᵐ[volume] fun x => |g x|) :
    euclideanFamilyMaximal G f = euclideanFamilyMaximal G g := by
  funext x
  unfold euclideanFamilyMaximal
  apply iSup_congr
  intro Q
  have hi : (∫ y in (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)), |f y|) =
      ∫ y in (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)), |g y| :=
    integral_congr_ae (ae_restrict_of_ae hfg)
  rw [hi]

/-- A weak logarithmic estimate on measurable nonnegative bounded tests with
bounded support extends to every signed locally integrable input. The finite
family and the endpoint coefficient and logarithmic order are unchanged. -/
theorem finite_endpoint_of_bounded_tests
    {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i))))
    (k : ℕ) (A : ℝ) (_hA : 0 ≤ A)
    (hweak : ∀ h : (Fin (∑ i, d i) → ℝ) → ℝ,
      Measurable h → (∀ x, 0 ≤ h x) → (∃ B : ℝ, ∀ x, h x ≤ B) →
      Bornology.IsBounded (Function.support h) → ∀ t : ℝ, 0 < t →
      volume {x | ENNReal.ofReal t < euclideanFamilyMaximal (G : Set _) h x} ≤
        ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
          (|h x| / t * (Real.log (Real.exp 1 + |h x| / t)) ^ k))
    (g : (Fin (∑ i, d i) → ℝ) → ℝ) (hg : LocallyIntegrable g volume)
    (t : ℝ) (ht : 0 < t) :
    volume {x | ENNReal.ofReal t < euclideanFamilyMaximal (G : Set _) g x} ≤
      ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
        (|g x| / t * (Real.log (Real.exp 1 + |g x| / t)) ^ k) := by
  let g0 : (Fin (∑ i, d i) → ℝ) → ℝ := hg.aestronglyMeasurable.mk g
  let h : (Fin (∑ i, d i) → ℝ) → ℝ := fun x => |g0 x|
  have hm : Measurable h := by
    have hm0 : Measurable (fun x => ‖g0 x‖) :=
      continuous_norm.measurable.comp hg.aestronglyMeasurable.measurable_mk
    simpa only [Real.norm_eq_abs] using hm0
  have hn (x) : 0 ≤ h x := abs_nonneg (g0 x)
  have hae : g =ᵐ[volume] g0 := hg.aestronglyMeasurable.ae_eq_mk
  have habs : (fun x => |g x|) =ᵐ[volume] h := hae.fun_comp abs
  have hgi : LocallyIntegrable (fun x => |g x|) volume := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    simpa only [IntegrableOn, Real.norm_eq_abs] using (hg.integrableOn_isCompact hK).norm
  have hhi : LocallyIntegrable h volume := hgi.congr habs
  have hdouble : (fun x => |g x|) =ᵐ[volume] fun x => |h x| :=
    habs.mono fun x he => he.trans (abs_of_nonneg (hn x)).symm
  have hmax := maximal_congr_abs_ae (G : Set _) g h hdouble
  have hi : (∫⁻ x, ENNReal.ofReal
      (|g x| / t * (Real.log (Real.exp 1 + |g x| / t)) ^ k)) =
      ∫⁻ x, ENNReal.ofReal
        (|h x| / t * (Real.log (Real.exp 1 + |h x| / t)) ^ k) :=
    lintegral_congr_ae (hdouble.fun_comp fun a : ℝ =>
      ENNReal.ofReal (a / t * (Real.log (Real.exp 1 + a / t)) ^ k))
  rw [hmax, hi]
  exact bounded_endpoint_nonnegative G k A hweak h hhi hm hn t ht

end ReyZygmund
