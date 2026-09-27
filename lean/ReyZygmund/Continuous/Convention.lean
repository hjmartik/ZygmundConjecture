import ReyZygmund.Continuous.HalfOpenBoundary
import ReyZygmund.Continuous.Measurability

/-! # Pointwise equality for the two half-open conventions

For a locally integrable input, a small translation of a rectangle preserves a
strict inequality for its average. Translating in one direction puts the point
inside a rectangle with the opposite half-open convention; the reverse translation
gives the other inequality. Thus the two suprema agree pointwise, even for the
uncountable family.
-/

open BoxIntegral MeasureTheory Filter
open scoped BigOperators Classical ENNReal Topology

namespace ReyZygmund.Continuous

open Geometry

private theorem eventually_abs_average_shiftBox_gt {k : ℕ}
    (Q : Box (Fin k)) (f : (Fin k → ℝ) → ℝ)
    (hf : LocallyIntegrable f volume) (lam : ℝ≥0∞)
    (h : lam < ENNReal.ofReal
      ((∫ y in (Q : Set (Fin k → ℝ)), |f y|) /
        volume.real (Q : Set (Fin k → ℝ)))) :
    ∀ᶠ t in 𝓝 (0 : ℝ), lam < ENNReal.ofReal
      ((∫ y in (shiftBox Q t : Set (Fin k → ℝ)), |f y|) /
        volume.real (Q : Set (Fin k → ℝ))) := by
  have hfabs : LocallyIntegrable (fun y => |f y|) volume := by
    simpa only [Real.norm_eq_abs] using
      locallyIntegrableOn_univ.mp (locallyIntegrableOn_univ.mpr hf).norm
  have havg : ContinuousAt (fun t : ℝ => ENNReal.ofReal
      ((∫ y in (shiftBox Q t : Set (Fin k → ℝ)), |f y|) /
        volume.real (Q : Set (Fin k → ℝ)))) 0 :=
    ENNReal.continuous_ofReal.continuousAt.comp
      ((continuousAt_integral_shiftBox Q (fun y => |f y|) hfabs).div_const _)
  exact continuousAt_const.eventually_lt havg (by simpa only [shiftBox_zero] using h)

private theorem lt_ico_continuous_maximal_of_lt_ioc
    {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf : LocallyIntegrable f volume)
    (x : Fin (∑ i, d i) → ℝ) (lam : ℝ≥0∞)
    (hx : lam < euclideanFamilyMaximal (continuousPhiRectangles d phi) f x) :
    lam < icoEuclideanFamilyMaximal (continuousPhiRectangles d phi) f x := by
  unfold euclideanFamilyMaximal at hx
  obtain ⟨R, hR⟩ := lt_iSup_iff.mp hx
  have hxR : x ∈ (flatProductBox R.1 : Set (Fin (∑ i, d i) → ℝ)) := by
    by_contra hnot
    rw [Set.indicator_of_notMem hnot, ENNReal.ofReal_zero] at hR
    exact (not_lt_of_ge (zero_le : (0 : ℝ≥0∞) ≤ lam)) hR
  rw [Set.indicator_of_mem hxR] at hR
  let Q := flatProductBox R.1
  have hlarge := eventually_abs_average_shiftBox_gt Q f hf lam hR
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
  have hxopen : x ∈ (flatProductBox R').Ioo := by
    rw [flatProductBox_shiftBox]
    intro j _
    exact ⟨hlow j, by have := (hxR j).2; dsimp [shiftBox]; linarith⟩
  have hxR' : x ∈ icoFlatProductBox R' :=
    fun j hj => ⟨(hxopen j hj).1.le, (hxopen j hj).2⟩
  unfold icoEuclideanFamilyMaximal
  apply lt_iSup_iff.mpr
  refine ⟨⟨R', hR'⟩, ?_⟩
  rw [Set.indicator_of_mem hxR', integral_icoFlatProductBox,
    volumeReal_icoFlatProductBox, flatProductBox_shiftBox, volumeReal_shiftBox]
  exact ht

private theorem lt_ioc_continuous_maximal_of_lt_ico
    {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf : LocallyIntegrable f volume)
    (x : Fin (∑ i, d i) → ℝ) (lam : ℝ≥0∞)
    (hx : lam < icoEuclideanFamilyMaximal (continuousPhiRectangles d phi) f x) :
    lam < euclideanFamilyMaximal (continuousPhiRectangles d phi) f x := by
  unfold icoEuclideanFamilyMaximal at hx
  obtain ⟨R, hR⟩ := lt_iSup_iff.mp hx
  have hxR : x ∈ icoFlatProductBox R.1 := by
    by_contra hnot
    rw [Set.indicator_of_notMem hnot, ENNReal.ofReal_zero] at hR
    exact (not_lt_of_ge (zero_le : (0 : ℝ≥0∞) ≤ lam)) hR
  rw [Set.indicator_of_mem hxR, integral_icoFlatProductBox,
    volumeReal_icoFlatProductBox] at hR
  let Q := flatProductBox R.1
  have hlarge := eventually_abs_average_shiftBox_gt Q f hf lam hR
  have hupper : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, x j < Q.upper j + t := by
    apply eventually_all.mpr
    intro j
    exact continuousAt_const.eventually_lt (continuousAt_const.add continuousAt_id)
      (by change x j < Q.upper j + 0
          simpa only [add_zero] using (hxR j (Set.mem_univ j)).2)
  have hneg : ∀ᶠ t in 𝓝[Set.Iio (0 : ℝ)] 0, t < 0 := self_mem_nhdsWithin
  obtain ⟨t, ⟨ht, hupp⟩, htneg⟩ :=
    (((hlarge.and hupper).filter_mono nhdsWithin_le_nhds).and hneg).exists
  let R' := fun i => shiftBox (R.1 i) t
  have hR' : R' ∈ continuousPhiRectangles d phi :=
    shiftBox_mem_continuousPhiRectangles phi R.1 R.2 t
  have hxopen : x ∈ (flatProductBox R').Ioo := by
    rw [flatProductBox_shiftBox]
    intro j _
    exact ⟨by have := (hxR j (Set.mem_univ j)).1; dsimp [shiftBox]; linarith, hupp j⟩
  have hxR' := (flatProductBox R').Ioo_subset_coe hxopen
  unfold euclideanFamilyMaximal
  apply lt_iSup_iff.mpr
  refine ⟨⟨R', hR'⟩, ?_⟩
  rw [Set.indicator_of_mem hxR', flatProductBox_shiftBox, volumeReal_shiftBox]
  exact ht

/-- The Ico and Ioc all-position maximal functions agree at every
point. No countability or monotonicity of the positive side function is needed. -/
theorem continuous_maximal_convention_eq {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf : LocallyIntegrable f volume) :
    icoEuclideanFamilyMaximal (continuousPhiRectangles d phi) f =
      euclideanFamilyMaximal (continuousPhiRectangles d phi) f := by
  funext x
  apply le_antisymm
  · by_contra h
    exact (lt_irrefl _) (lt_ioc_continuous_maximal_of_lt_ico phi f hf x _
      (lt_of_not_ge h))
  · by_contra h
    exact (lt_irrefl _) (lt_ico_continuous_maximal_of_lt_ioc phi f hf x _
      (lt_of_not_ge h))

/-- Measurability belongs to the Ico supremum, not a representative. -/
theorem measurable_continuous_ico_maximal {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf : LocallyIntegrable f volume) :
    Measurable (icoEuclideanFamilyMaximal (continuousPhiRectangles d phi) f) := by
  rw [continuous_maximal_convention_eq phi f hf]
  exact measurable_continuous_maximal phi f hf

/-- Strict-level measures agree for every extended threshold. -/
theorem continuous_maximal_convention_levelset_measure
    {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf : LocallyIntegrable f volume)
    (lam : ℝ≥0∞) :
    volume {x | lam < icoEuclideanFamilyMaximal (continuousPhiRectangles d phi) f x} =
      volume {x | lam < euclideanFamilyMaximal (continuousPhiRectangles d phi) f x} := by
  rw [continuous_maximal_convention_eq phi f hf]

end ReyZygmund.Continuous
