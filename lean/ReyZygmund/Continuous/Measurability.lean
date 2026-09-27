import ReyZygmund.Geometry.PhiRectangles
import ReyZygmund.Maximal.Euclidean
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Semicontinuity.Basic

/-! # Measurability of the maximal function at arbitrary positions

Local integrability makes the integral over a rectangle continuous under
translation. A rectangle with average above a threshold can therefore be moved
slightly to put the point in its interior without changing its side lengths or
losing the inequality. This proves openness of the strict level sets without
regularity of the side function. -/

open BoxIntegral MeasureTheory Filter
open scoped BigOperators Classical ENNReal Topology

namespace ReyZygmund.Continuous

open Geometry

/-- Translation by the same real amount in every scalar coordinate. -/
def shiftBox {k : ℕ} (Q : Box (Fin k)) (t : ℝ) : Box (Fin k) where
  lower j := Q.lower j + t
  upper j := Q.upper j + t
  lower_lt_upper j := by have := Q.lower_lt_upper j; linarith

@[simp] theorem shiftBox_zero {k : ℕ} (Q : Box (Fin k)) : shiftBox Q 0 = Q := by
  cases Q
  simp [shiftBox]

theorem volumeReal_shiftBox {k : ℕ} (Q : Box (Fin k)) (t : ℝ) :
    volume.real (shiftBox Q t : Set (Fin k → ℝ)) = volume.real (Q : Set (Fin k → ℝ)) := by
  simp only [measureReal_def, Box.volume_apply', shiftBox]
  congr 1
  funext j
  ring

private theorem eventually_mem_shiftBox {k : ℕ} (Q : Box (Fin k))
    (y : Fin k → ℝ) (hy : y ∈ Q.Ioo) :
    ∀ᶠ t in 𝓝 (0 : ℝ), y ∈ (shiftBox Q t : Set (Fin k → ℝ)) := by
  have h (j : Fin k) : ∀ᶠ t in 𝓝 (0 : ℝ),
      Q.lower j + t < y j ∧ y j < Q.upper j + t := by
    have hj := hy j (Set.mem_univ j)
    exact ((continuousAt_const.add continuousAt_id).eventually_lt continuousAt_const
      (by simpa using hj.1)).and
      (continuousAt_const.eventually_lt (continuousAt_const.add continuousAt_id)
        (by simpa using hj.2))
  filter_upwards [eventually_all.mpr h] with t ht
  exact fun j => ⟨(ht j).1, (ht j).2.le⟩

private theorem eventually_notMem_shiftBox {k : ℕ} (Q : Box (Fin k))
    (y : Fin k → ℝ) (hy : y ∉ Q.Icc) :
    ∀ᶠ t in 𝓝 (0 : ℝ), y ∉ (shiftBox Q t : Set (Fin k → ℝ)) := by
  have hex : ∃ j, y j < Q.lower j ∨ Q.upper j < y j := by
    by_contra h
    push Not at h
    exact hy ⟨fun j => (h j).1, fun j => (h j).2⟩
  obtain ⟨j, hj | hj⟩ := hex
  · have h : ∀ᶠ t in 𝓝 (0 : ℝ), y j < Q.lower j + t :=
      continuousAt_const.eventually_lt (continuousAt_const.add continuousAt_id)
        (by simpa using hj)
    filter_upwards [h] with t ht
    exact fun hm => (not_lt_of_ge (hm j).1.le) ht
  · have h : ∀ᶠ t in 𝓝 (0 : ℝ), Q.upper j + t < y j :=
      (continuousAt_const.add continuousAt_id).eventually_lt continuousAt_const
        (by simpa using hj)
    filter_upwards [h] with t ht
    exact fun hm => (not_lt_of_ge (hm j).2) ht

/-- The translated box integral is continuous at zero for every locally
integrable signed function, including zero-dimensional boxes. -/
theorem continuousAt_integral_shiftBox {k : ℕ} (Q : Box (Fin k))
    (f : (Fin k → ℝ) → ℝ) (hf : LocallyIntegrable f volume) :
    ContinuousAt (fun t : ℝ => ∫ y in (shiftBox Q t : Set (Fin k → ℝ)), f y) 0 := by
  let K : Box (Fin k) :=
    ⟨fun j => Q.lower j - 1, fun j => Q.upper j + 1,
      fun j => by have := Q.lower_lt_upper j; linarith⟩
  have hK : IntegrableOn (fun y => |f y|) K.Icc volume :=
    (hf.integrableOn_isCompact K.isCompact_Icc).abs
  have hbound : Integrable (K.Icc.indicator (fun y => |f y|)) volume :=
    hK.integrable_indicator K.isCompact_Icc.measurableSet
  have hmeas (t : ℝ) : AEStronglyMeasurable
      ((shiftBox Q t : Set (Fin k → ℝ)).indicator f) volume :=
    hf.aestronglyMeasurable.indicator (shiftBox Q t).measurableSet_coe
  have hdom : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ᵐ y ∂volume,
      ‖(shiftBox Q t : Set (Fin k → ℝ)).indicator f y‖ ≤
        K.Icc.indicator (fun y => |f y|) y := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
      with t ht
    apply Filter.Eventually.of_forall
    intro y
    by_cases hy : y ∈ (shiftBox Q t : Set (Fin k → ℝ))
    · have hyK : y ∈ K.Icc :=
        ⟨fun j => by have := (hy j).1; dsimp [shiftBox] at this; dsimp [K]; linarith [ht.1],
         fun j => by have := (hy j).2; dsimp [shiftBox] at this; dsimp [K]; linarith [ht.2]⟩
      simp [Set.indicator_of_mem hy, Set.indicator_of_mem hyK, Real.norm_eq_abs]
    · rw [Set.indicator_of_notMem hy, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) y
  have hae : Q.Ioo =ᵐ[volume] Q.Icc := by
    exact Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ : Fin k => (volume : Measure ℝ))
      (f := Q.lower) (g := Q.upper)
  have hlim : ∀ᵐ y ∂volume, Tendsto
      (fun t : ℝ => (shiftBox Q t : Set (Fin k → ℝ)).indicator f y)
      (𝓝 0) (𝓝 ((Q : Set (Fin k → ℝ)).indicator f y)) := by
    filter_upwards [Filter.eventuallyEqSet_iff.mp hae] with y hy
    by_cases hclosed : y ∈ Q.Icc
    · have hopen := hy.mpr hclosed
      have hQ : y ∈ (Q : Set (Fin k → ℝ)) := Q.Ioo_subset_coe hopen
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_mem_shiftBox Q y hopen] with t ht
      simp only [Set.indicator_of_mem ht, Set.indicator_of_mem hQ]
    · have hQ : y ∉ (Q : Set (Fin k → ℝ)) := fun h => hclosed (Box.coe_subset_Icc h)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_notMem_shiftBox Q y hclosed] with t ht
      simp only [Set.indicator_of_notMem ht, Set.indicator_of_notMem hQ]
  have h := tendsto_integral_filter_of_dominated_convergence
    (K.Icc.indicator (fun y => |f y|)) (Filter.Eventually.of_forall hmeas) hdom hbound hlim
  change Tendsto _ (𝓝 0) (𝓝 (∫ y in (shiftBox Q 0 : Set (Fin k → ℝ)), f y))
  simpa only [integral_indicator (shiftBox Q _).measurableSet_coe,
    integral_indicator Q.measurableSet_coe, shiftBox_zero] using h

theorem flatProductBox_shiftBox {m : ℕ} {d : Fin m → ℕ}
    (R : ∀ i, Box (Fin (d i))) (t : ℝ) :
    flatProductBox (fun i => shiftBox (R i) t) = shiftBox (flatProductBox R) t := by
  apply Box.ext
  intro x
  change (∀ j, _ < x j ∧ x j ≤ _) ↔ (∀ j, _ < x j ∧ x j ≤ _)
  apply forall_congr'
  intro j
  obtain ⟨⟨i, a⟩, rfl⟩ := (finSigmaFinEquiv (n := d)).surjective j
  simp only [flatProductBox, shiftBox, flattenCoordinates_apply]

theorem shiftBox_mem_continuousPhiRectangles {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (R : ∀ i, Box (Fin (d i))) (hR : R ∈ continuousPhiRectangles d phi) (t : ℝ) :
    (fun i => shiftBox (R i) t) ∈ continuousPhiRectangles d phi := by
  obtain ⟨s, hs⟩ := hR
  refine ⟨s, fun i a => ?_⟩
  dsimp [shiftBox]
  rw [add_sub_add_right_eq_sub]
  exact hs i a

/-- Every strict extended-real level set of the maximal function is open, including at
points initially on an upper face of the averaging rectangle. -/
theorem isOpen_continuous_maximal_levelset {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf : LocallyIntegrable f volume)
    (lam : ℝ≥0∞) :
    IsOpen {x | lam < euclideanFamilyMaximal (continuousPhiRectangles d phi) f x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  change lam < euclideanFamilyMaximal (continuousPhiRectangles d phi) f x at hx
  unfold euclideanFamilyMaximal at hx
  obtain ⟨R, hR⟩ := lt_iSup_iff.mp hx
  have hxR : x ∈ (flatProductBox R.1 : Set (Fin (∑ i, d i) → ℝ)) := by
    by_contra hnot
    rw [Set.indicator_of_notMem hnot, ENNReal.ofReal_zero] at hR
    exact (not_lt_of_ge (zero_le : (0 : ℝ≥0∞) ≤ lam)) hR
  rw [Set.indicator_of_mem hxR] at hR
  let Q := flatProductBox R.1
  have hfabs : LocallyIntegrable (fun y => |f y|) volume := by
    simpa only [Real.norm_eq_abs] using
      locallyIntegrableOn_univ.mp (locallyIntegrableOn_univ.mpr hf).norm
  have havg : ContinuousAt (fun t : ℝ => ENNReal.ofReal
      ((∫ y in (shiftBox Q t : Set (Fin (∑ i, d i) → ℝ)), |f y|) /
        volume.real (Q : Set (Fin (∑ i, d i) → ℝ)))) 0 :=
    ENNReal.continuous_ofReal.continuousAt.comp
      ((continuousAt_integral_shiftBox Q (fun y => |f y|) hfabs).div_const _)
  have hlarge : ∀ᶠ t in 𝓝 (0 : ℝ), lam < ENNReal.ofReal
      ((∫ y in (shiftBox Q t : Set (Fin (∑ i, d i) → ℝ)), |f y|) /
        volume.real (Q : Set (Fin (∑ i, d i) → ℝ))) :=
    continuousAt_const.eventually_lt havg (by simpa only [shiftBox_zero] using hR)
  have hlower : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, Q.lower j + t < x j := by
    apply eventually_all.mpr
    intro j
    exact (continuousAt_const.add continuousAt_id).eventually_lt continuousAt_const
      (by change Q.lower j + 0 < x j; simpa only [add_zero] using (hxR j).1)
  have hpos : ∀ᶠ t in 𝓝[Set.Ioi (0 : ℝ)] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ⟨ht, hlow⟩, htpos⟩ :=
    (((hlarge.and hlower).filter_mono nhdsWithin_le_nhds).and hpos).exists
  let R' := fun i => shiftBox (R.1 i) t
  have hR' : R' ∈ continuousPhiRectangles d phi :=
    shiftBox_mem_continuousPhiRectangles phi R.1 R.2 t
  have hopen : IsOpen (flatProductBox R').Ioo :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hxopen : x ∈ (flatProductBox R').Ioo := by
    rw [flatProductBox_shiftBox]
    intro j _
    exact ⟨hlow j, by have := (hxR j).2; dsimp [shiftBox]; linarith⟩
  apply Filter.mem_of_superset (hopen.mem_nhds hxopen)
  intro y hy
  have hyR' := (flatProductBox R').Ioo_subset_coe hy
  change lam < euclideanFamilyMaximal (continuousPhiRectangles d phi) f y
  unfold euclideanFamilyMaximal
  apply lt_iSup_iff.mpr
  refine ⟨⟨R', hR'⟩, ?_⟩
  rw [Set.indicator_of_mem hyR', flatProductBox_shiftBox, volumeReal_shiftBox]
  exact ht

/-- Borel measurability of the all-position operator; no countable
replacement family or measurable representative is substituted. -/
theorem measurable_continuous_maximal {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf : LocallyIntegrable f volume) :
    Measurable (euclideanFamilyMaximal (continuousPhiRectangles d phi) f) :=
  measurable_of_Ioi (fun lam => (isOpen_continuous_maximal_levelset phi f hf lam).measurableSet)

end ReyZygmund.Continuous
