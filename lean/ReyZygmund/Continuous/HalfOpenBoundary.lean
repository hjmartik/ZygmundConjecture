import ReyZygmund.Maximal.Euclidean
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Half-open conventions for countable rectangle families

The paper uses `[lower, upper)` and Mathlib uses `(lower, upper]`. Rectangles with
the same corners have the same restricted Lebesgue measure. Their supported
averages agree outside the boundaries, and one null set suffices for a countable
family. The uncountable family is treated separately in `Convention.lean`.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Continuous

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- The `[lower, upper)` rectangle with the existing flattened corners. -/
noncomputable def icoFlatProductBox (Q : ∀ i, Box (Fin (d i))) :
    Set (Fin (∑ i, d i) → ℝ) :=
  Set.pi Set.univ (fun j =>
    Set.Ico ((flatProductBox Q).lower j) ((flatProductBox Q).upper j))

theorem measurableSet_icoFlatProductBox (Q : ∀ i, Box (Fin (d i))) :
    MeasurableSet (icoFlatProductBox Q) :=
  MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Ico)

/-- Both half-open conventions agree with the same closed box almost everywhere. -/
theorem icoFlatProductBox_ae_eq (Q : ∀ i, Box (Fin (d i))) :
    icoFlatProductBox Q =ᵐ[volume]
      (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) := by
  rw [Box.coe_eq_pi]
  exact Measure.univ_pi_Ico_ae_eq_Icc.trans Measure.univ_pi_Ioc_ae_eq_Icc.symm

theorem volume_icoFlatProductBox (Q : ∀ i, Box (Fin (d i))) :
    volume (icoFlatProductBox Q) =
      volume (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) :=
  measure_congr (icoFlatProductBox_ae_eq Q)

theorem volumeReal_icoFlatProductBox (Q : ∀ i, Box (Fin (d i))) :
    volume.real (icoFlatProductBox Q) =
      volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) :=
  congrArg ENNReal.toReal (volume_icoFlatProductBox Q)

theorem icoFlatProductBox_volume_pos_finite (Q : ∀ i, Box (Fin (d i))) :
    0 < volume.real (icoFlatProductBox Q) ∧ volume (icoFlatProductBox Q) < ∞ := by
  rw [volumeReal_icoFlatProductBox, volume_icoFlatProductBox]
  exact ⟨box_volume_pos (flatProductBox Q), (flatProductBox Q).measure_coe_lt_top volume⟩

/-- Equality of the restricted measures gives equality of integrals for any signed
input. The next lemma establishes integrability for the analytic application. -/
theorem integral_icoFlatProductBox (Q : ∀ i, Box (Fin (d i)))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) :
    (∫ x in icoFlatProductBox Q, f x) =
      ∫ x in (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)), f x :=
  setIntegral_congr_set (icoFlatProductBox_ae_eq Q)

theorem integrableOn_icoFlatProductBox (Q : ∀ i, Box (Fin (d i)))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf : LocallyIntegrable f volume) :
    IntegrableOn f (icoFlatProductBox Q) volume := by
  have hQ : IntegrableOn f
      (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) volume :=
    (hf.integrableOn_isCompact (flatProductBox Q).isCompact_Icc).mono_set Box.coe_subset_Icc
  exact hQ.congr_set_ae (icoFlatProductBox_ae_eq Q)

/-- The supremum of supported averages of `|f|` with the paper's `[lower, upper)`
convention. Values may be infinite. -/
noncomputable def icoEuclideanFamilyMaximal
    (G : Set (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (x : Fin (∑ i, d i) → ℝ) : ℝ≥0∞ :=
  ⨆ Q : G, ENNReal.ofReal
    ((icoFlatProductBox Q.1).indicator
      (fun _ => (∫ y in icoFlatProductBox Q.1, |f y|) /
        volume.real (icoFlatProductBox Q.1)) x)

theorem measurable_icoEuclideanFamilyMaximal
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G.Countable)
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) : Measurable (icoEuclideanFamilyMaximal G f) := by
  have := hG.to_subtype
  exact Measurable.iSup (fun Q : G =>
    ((measurable_const : Measurable (fun _ : Fin (∑ i, d i) → ℝ =>
      (∫ y in icoFlatProductBox Q.1, |f y|) / volume.real (icoFlatProductBox Q.1))).indicator
        (measurableSet_icoFlatProductBox Q.1)).ennreal_ofReal)

/-- Countability gives a single full-measure set on which all rectangle
memberships and hence all supported averages agree simultaneously. -/
theorem icoEuclideanFamilyMaximal_ae_eq
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G.Countable)
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) :
    icoEuclideanFamilyMaximal G f =ᵐ[volume] euclideanFamilyMaximal G f := by
  have := hG.to_subtype
  have hmem (Q : G) : ∀ᵐ x ∂volume,
      x ∈ icoFlatProductBox Q.1 ↔
        x ∈ (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)) :=
    Filter.eventuallyEqSet_iff.mp (icoFlatProductBox_ae_eq Q.1)
  filter_upwards [ae_all_iff.mpr hmem] with x hx
  unfold icoEuclideanFamilyMaximal euclideanFamilyMaximal
  apply iSup_congr
  intro Q
  simp only [integral_icoFlatProductBox, volumeReal_icoFlatProductBox,
    Set.indicator_apply, hx Q]

/-- In particular the strict positive-level measures agree. Neither
finite maximal values nor a finite total shadow measure are assumed. -/
theorem icoEuclideanFamilyMaximal_levelset_measure
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G.Countable)
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (lam : ℝ) (_hlam : 0 < lam) :
    volume {x | ENNReal.ofReal lam < icoEuclideanFamilyMaximal G f x} =
      volume {x | ENNReal.ofReal lam < euclideanFamilyMaximal G f x} := by
  apply measure_congr
  apply Filter.eventuallyEqSet_iff.mpr
  filter_upwards [icoEuclideanFamilyMaximal_ae_eq G hG f] with x hx
  rw [hx]

end ReyZygmund.Continuous
