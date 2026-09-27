import ReyZygmund.Overlap.Finite
import ReyZygmund.Maximal.FiniteIdentification
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Finite sparse pairing

Use the disjoint subsets establishing sparseness to bound the overlap pairing by
the integral of the finite maximal function on the shadow. This step needs neither
a grid nor incomparability.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Overlap

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem pairing_integrable_and_integral
    (G : Finset (∀ i, Box (Fin (d i))))
    (g : (Fin (∑ i, d i) → ℝ) → ℝ)
    (hgi : ∀ R ∈ G, IntegrableOn g (flatProductBox R) volume) :
    Integrable (fun x => finiteOverlap G x * g x) volume ∧
      (∫ x, finiteOverlap G x * g x) =
        ∑ R ∈ G, ∫ x in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), g x := by
  have heq : (fun x => finiteOverlap G x * g x) =
      (fun x => ∑ R ∈ G,
        (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)).indicator g x) := by
    funext x
    rw [finiteOverlap, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro R _
    by_cases hx : x ∈ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))
    · simp only [Set.indicator_of_mem hx, one_mul]
    · simp only [Set.indicator_of_notMem hx, zero_mul]
  have hi (R) (hR : R ∈ G) :
      Integrable ((flatProductBox R : Set (Fin (∑ i, d i) → ℝ)).indicator g) volume :=
    (hgi R hR).integrable_indicator (flatProductBox R).measurableSet_coe
  constructor
  · rw [heq]
    exact integrable_finsetSum G hi
  · rw [heq, integral_finsetSum G hi]
    exact Finset.sum_congr rfl (fun R _ => integral_indicator (flatProductBox R).measurableSet_coe)

private theorem absolute_mean_le_finite_maximal
    (G : Finset (∀ i, Box (Fin (d i))))
    (g : (Fin (∑ i, d i) → ℝ) → ℝ)
    (R : ∀ i, Box (Fin (d i))) (hR : R ∈ G)
    (x : Fin (∑ i, d i) → ℝ) (hx : x ∈ (flatProductBox R : Set _)) :
    (∫ y in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), |g y|) /
        volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤
      (euclideanFamilyMaximal (G : Set _) g x).toReal := by
  have hmean : 0 ≤
      (∫ y in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), |g y|) /
        volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) :=
    div_nonneg (integral_nonneg (fun _ => abs_nonneg _)) ENNReal.toReal_nonneg
  have hsup : ENNReal.ofReal
      ((∫ y in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), |g y|) /
        volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) ≤
      euclideanFamilyMaximal (G : Set _) g x := by
    unfold euclideanFamilyMaximal
    apply le_iSup_of_le (⟨R, hR⟩ : (G : Set _))
    rw [Set.indicator_of_mem hx]
  simpa only [ENNReal.toReal_ofReal hmean] using
    ENNReal.toReal_mono (euclideanFamilyMaximal_finset_lt_top G g x).ne hsup

/-- The finite sparse-pairing estimate on Euclidean rectangles.
All integrability is derived from the local input integrability and the
finite family; no condition is imposed outside its shadow. -/
theorem finite_sparse_pairing
    (G : Finset (∀ i, Box (Fin (d i)))) (eta : ℝ) (heta : 0 < eta)
    (E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ))
    (hEmeas : ∀ R ∈ G, MeasurableSet (E R))
    (hEsub : ∀ R ∈ G,
      E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)))
    (hEdis : Set.Pairwise (G : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (E R) (E S)))
    (hEmass : ∀ R ∈ G,
      ENNReal.ofReal eta * volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤
        volume (E R))
    (g : (Fin (∑ i, d i) → ℝ) → ℝ)
    (hg0 : ∀ x ∈ finiteShadow G, 0 ≤ g x)
    (hgi : ∀ R ∈ G, IntegrableOn g (flatProductBox R) volume) :
    eta * (∫ x, finiteOverlap G x * g x) ≤
      ∫ x in finiteShadow G, (euclideanFamilyMaximal (G : Set _) g x).toReal := by
  obtain ⟨_, hpair⟩ := pairing_integrable_and_integral G g hgi
  have hM := integrable_euclideanFamilyMaximal_finset G g
  have hterm (R) (hR : R ∈ G) :
      eta * (∫ x in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), g x) ≤
        ∫ x in E R, (euclideanFamilyMaximal (G : Set _) g x).toReal := by
    have hEfinite : volume (E R) < ∞ :=
      lt_of_le_of_lt (measure_mono (hEsub R hR))
        (flatProductBox R).isBounded.measure_lt_top
    have hmass : eta * volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤
        volume.real (E R) := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal heta.le, measureReal_def] using
        ENNReal.toReal_mono hEfinite.ne (hEmass R hR)
    have hvol := box_volume_pos (flatProductBox R)
    have hnonneg : ∀ x ∈ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), 0 ≤ g x :=
      fun x hx => hg0 x (flatProductBox_subset_finiteShadow G R hR hx)
    have habs :
        (∫ x in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), |g x|) =
          ∫ x in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), g x :=
      setIntegral_congr_fun (flatProductBox R).measurableSet_coe
        (fun x hx => abs_of_nonneg (hnonneg x hx))
    have hmean : 0 ≤
        (∫ x in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), g x) /
          volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) :=
      div_nonneg (setIntegral_nonneg (flatProductBox R).measurableSet_coe hnonneg) hvol.le
    have hpoint (x) (hx : x ∈ E R) :
        (∫ y in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), g y) /
            volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤
          (euclideanFamilyMaximal (G : Set _) g x).toReal := by
      rw [← habs]
      exact absolute_mean_le_finite_maximal G g R hR x (hEsub R hR hx)
    calc
      _ = (eta * volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) *
          ((∫ x in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), g x) /
            volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) := by
        rw [mul_assoc, mul_comm (volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) _,
          div_mul_cancel₀ _ hvol.ne']
      _ ≤ volume.real (E R) *
          ((∫ x in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), g x) /
            volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) :=
        mul_le_mul_of_nonneg_right hmass hmean
      _ ≤ _ := by
        simpa only [smul_eq_mul] using
          setIntegral_ge_of_const_le (hEmeas R hR) hEfinite.ne hpoint hM.integrableOn
  have hsub : (⋃ R ∈ G, E R) ⊆ finiteShadow G :=
    Set.iUnion_subset (fun R => Set.iUnion_subset (fun hR =>
      (hEsub R hR).trans (flatProductBox_subset_finiteShadow G R hR)))
  calc
    _ = ∑ R ∈ G, eta *
        (∫ x in (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)), g x) := by
      rw [hpair, Finset.mul_sum]
    _ ≤ ∑ R ∈ G, ∫ x in E R, (euclideanFamilyMaximal (G : Set _) g x).toReal :=
      Finset.sum_le_sum hterm
    _ = ∫ x in ⋃ R ∈ G, E R, (euclideanFamilyMaximal (G : Set _) g x).toReal :=
      (integral_biUnion_finset G hEmeas hEdis (fun _ _ => hM.integrableOn)).symm
    _ ≤ _ := setIntegral_mono_set hM.integrableOn
      (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
      (Filter.Eventually.of_forall (fun _ hx => hsub hx))

end ReyZygmund.Overlap
