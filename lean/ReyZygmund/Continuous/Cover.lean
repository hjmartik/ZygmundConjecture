import ReyZygmund.Geometry.PhiRectangles
import ReyZygmund.Geometry.PrescribedCover
import ReyZygmund.Geometry.RoundedScales
import ReyZygmund.Maximal.Euclidean
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! # Covering and pointwise maximal domination

Each rectangle is covered at the prescribed rounded side lengths in one of the
shifted product grids. Comparing Lebesgue volumes and averages gives pointwise
maximal domination for locally integrable inputs. Positivity of the side function
suffices here; monotonicity and regularity are not needed.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Continuous

open Geometry

private theorem box_volume_le_of_width_le {k : ℕ} (R I : Box (Fin k))
    (hwidth : ∀ j, I.upper j - I.lower j ≤ 8 * (R.upper j - R.lower j)) :
    volume.real (I : Set (Fin k → ℝ)) ≤
      (8 : ℝ) ^ k * volume.real (R : Set (Fin k → ℝ)) := by
  simp only [measureReal_def, Box.volume_apply']
  calc
    Finset.univ.prod (fun j : Fin k => I.upper j - I.lower j) ≤
        Finset.univ.prod (fun j : Fin k => 8 * (R.upper j - R.lower j)) :=
      Finset.prod_le_prod₀ (fun j _ => (sub_pos.mpr (I.lower_lt_upper j)).le)
        (fun j _ => hwidth j)
    _ = (8 : ℝ) ^ k * Finset.univ.prod (fun j : Fin k => R.upper j - R.lower j) := by
      rw [Finset.prod_mul_distrib]
      simp

/-- Every continuous rectangle has a rounded-grid cover with the
paper's dimensional volume factor. Zero-dimensional blocks are allowed. -/
theorem continuous_rectangle_cover {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (R : ∀ i, Box (Fin (d i))) (hR : R ∈ continuousPhiRectangles d phi) :
    ∃ (τ : ∀ i, Fin (d i) → Fin 3) (I : ∀ i, Box (Fin (d i))),
      I ∈ roundedGridRectangles (fun i => shiftedDyadicGrid (d i) (τ i)) phi ∧
      (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ⊆ flatProductBox I ∧
      volume.real (flatProductBox I : Set (Fin (∑ i, d i) → ℝ)) /
          volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤
        (8 : ℝ) ^ (∑ i, d i) := by
  obtain ⟨s, hwidth⟩ := hR
  let side : Fin (n + 1) → ℝ := Fin.snoc (fun j => (s j).1) (phi s).1
  have hside (i : Fin (n + 1)) : 0 < side i := by
    exact Fin.lastCases (by simpa only [side, Fin.snoc_last, Set.mem_Ioi] using (phi s).2)
      (fun j => by simpa only [side, Fin.snoc_castSucc, Set.mem_Ioi] using (s j).2) i
  have hcover (i : Fin (n + 1)) :=
    prescribed_dyadic_cover (R i) (side i) (hside i) (hwidth i)
  choose τ I hgrid hsub hwidthI using hcover
  refine ⟨τ, I, ?_, ?_, ?_⟩
  · refine ⟨fun i => roundedScale (side i), ?_, hgrid⟩
    refine ⟨s, ?_⟩
    funext i
    exact Fin.lastCases (by simp [side]) (fun j => by simp [side]) i
  · intro x hx
    obtain ⟨y, rfl⟩ := (flattenCoordinates d).surjective x
    change flattenCoordinates d y ∈ flatProductBox R at hx
    change flattenCoordinates d y ∈ flatProductBox I
    rw [mem_flatProductBox, mem_productBox] at hx ⊢
    exact fun i => hsub i (Box.coe_subset_Icc (hx i))
  · apply (div_le_iff₀ (box_volume_pos (flatProductBox R))).mpr
    apply box_volume_le_of_width_le (flatProductBox R) (flatProductBox I)
    intro j
    obtain ⟨⟨i, a⟩, rfl⟩ := (finSigmaFinEquiv (n := d)).surjective j
    simp only [flatProductBox, flattenCoordinates_apply]
    rw [hwidthI i a, hwidth i a]
    exact (roundedScale_bounds (hside i)).2.le

private theorem integrableOn_abs_box {k : ℕ} (f : (Fin k → ℝ) → ℝ)
    (hf : LocallyIntegrable f volume) (Q : Box (Fin k)) :
    IntegrableOn (fun x => |f x|) (Q : Set (Fin k → ℝ)) volume := by
  have hQ : IntegrableOn f (Q : Set (Fin k → ℝ)) volume :=
    (hf.integrableOn_isCompact Q.isCompact_Icc).mono_set Box.coe_subset_Icc
  exact (show Integrable f (volume.restrict (Q : Set (Fin k → ℝ))) from hQ).abs

private theorem average_abs_le_of_cover {k : ℕ} (R I : Box (Fin k))
    (f : (Fin k → ℝ) → ℝ) (hf : LocallyIntegrable f volume)
    (hsub : (R : Set (Fin k → ℝ)) ⊆ I) (A : ℝ)
    (hvol : volume.real (I : Set (Fin k → ℝ)) /
      volume.real (R : Set (Fin k → ℝ)) ≤ A) :
    (∫ x in (R : Set (Fin k → ℝ)), |f x|) / volume.real (R : Set (Fin k → ℝ)) ≤
      A * ((∫ x in (I : Set (Fin k → ℝ)), |f x|) /
        volume.real (I : Set (Fin k → ℝ))) := by
  have hI := integrableOn_abs_box f hf I
  have hmono : (∫ x in (R : Set (Fin k → ℝ)), |f x|) ≤
      ∫ x in (I : Set (Fin k → ℝ)), |f x| :=
    setIntegral_mono_set hI (Filter.Eventually.of_forall (fun x => abs_nonneg (f x)))
      (Filter.Eventually.of_forall hsub)
  have havg : 0 ≤ (∫ x in (I : Set (Fin k → ℝ)), |f x|) /
      volume.real (I : Set (Fin k → ℝ)) :=
    div_nonneg (integral_nonneg (fun x => abs_nonneg (f x))) (box_volume_pos I).le
  calc
    _ ≤ (∫ x in (I : Set (Fin k → ℝ)), |f x|) /
        volume.real (R : Set (Fin k → ℝ)) :=
      div_le_div_of_nonneg_right hmono (box_volume_pos R).le
    _ = (volume.real (I : Set (Fin k → ℝ)) / volume.real (R : Set (Fin k → ℝ))) *
        ((∫ x in (I : Set (Fin k → ℝ)), |f x|) /
          volume.real (I : Set (Fin k → ℝ))) :=
      (div_mul_div_cancel₀' (ne_of_gt (box_volume_pos I)) _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hvol havg

/-- Pointwise domination by the finite collection of rounded
families. The maxima remain extended-valued; no finiteness is assumed. -/
theorem continuous_maximal_le_rounded {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf : LocallyIntegrable f volume)
    (x : Fin (∑ i, d i) → ℝ) :
    euclideanFamilyMaximal (continuousPhiRectangles d phi) f x ≤
      ENNReal.ofReal ((8 : ℝ) ^ (∑ i, d i)) *
        ⨆ τ : (∀ i, Fin (d i) → Fin 3),
          euclideanFamilyMaximal
            (roundedGridRectangles (fun i => shiftedDyadicGrid (d i) (τ i)) phi) f x := by
  unfold euclideanFamilyMaximal
  apply iSup_le
  intro R
  by_cases hx : x ∈ (flatProductBox R.1 : Set (Fin (∑ i, d i) → ℝ))
  · obtain ⟨τ, I, hI, hsub, hvol⟩ := continuous_rectangle_cover phi R.1 R.2
    have hxI : x ∈ (flatProductBox I : Set (Fin (∑ i, d i) → ℝ)) := hsub hx
    rw [Set.indicator_of_mem hx]
    have hmean := average_abs_le_of_cover (flatProductBox R.1) (flatProductBox I)
      f hf hsub ((8 : ℝ) ^ (∑ i, d i)) hvol
    have hImax : ENNReal.ofReal
        ((∫ y in (flatProductBox I : Set (Fin (∑ i, d i) → ℝ)), |f y|) /
          volume.real (flatProductBox I : Set (Fin (∑ i, d i) → ℝ))) ≤
        euclideanFamilyMaximal
          (roundedGridRectangles (fun i => shiftedDyadicGrid (d i) (τ i)) phi) f x := by
      have h := le_iSup (fun Q : roundedGridRectangles
          (fun i => shiftedDyadicGrid (d i) (τ i)) phi => ENNReal.ofReal
        ((flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)).indicator
          (fun _ => (∫ y in (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)), |f y|) /
            volume.real (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ))) x)) ⟨I, hI⟩
      simpa only [euclideanFamilyMaximal, Set.indicator_of_mem hxI] using h
    have hτ := le_iSup (fun σ : (∀ i, Fin (d i) → Fin 3) =>
      euclideanFamilyMaximal
        (roundedGridRectangles (fun i => shiftedDyadicGrid (d i) (σ i)) phi) f x) τ
    calc
      _ ≤ ENNReal.ofReal (((8 : ℝ) ^ (∑ i, d i)) *
          ((∫ y in (flatProductBox I : Set (Fin (∑ i, d i) → ℝ)), |f y|) /
            volume.real (flatProductBox I : Set (Fin (∑ i, d i) → ℝ)))) :=
        ENNReal.ofReal_le_ofReal hmean
      _ = ENNReal.ofReal ((8 : ℝ) ^ (∑ i, d i)) * ENNReal.ofReal
          ((∫ y in (flatProductBox I : Set (Fin (∑ i, d i) → ℝ)), |f y|) /
            volume.real (flatProductBox I : Set (Fin (∑ i, d i) → ℝ))) :=
        ENNReal.ofReal_mul (pow_nonneg (by norm_num) _)
      _ ≤ _ := mul_le_mul_right (hImax.trans hτ) _
  · rw [Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
    exact zero_le

end ReyZygmund.Continuous
