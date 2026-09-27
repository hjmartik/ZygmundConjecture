import ReyZygmund.Maximal.PartialSigned
import ReyZygmund.Projection.Representation

/-!
# The pointwise maximal bound from the common projection

The exact signed representation has one term for each proper coordinate
subset. Each such term is bounded by a signed maximum omitting one coordinate.
The positive family maximum is used only on the original nonnegative input.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- The pointwise maximal bound for the finite averaging family and common projection,
without incomparability or strict positivity. -/
theorem finite_representation_maximal
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (f : boundedMeasurableFunctions d)
    (hf : ProductLeafConstant I N f.1)
    (hs : ∀ x, x ∉ productBox I → f.1 x = 0)
    (hpos : ∀ x ∈ productBox I, 0 ≤ f.1 x)
    (x : ProductPoint d) (hx : x ∈ productBox I) :
    finiteFamilyMaximal (averagingRectangles I N G) f x ≤
      (2 : ℝ) ^ m * ∑ j,
        finiteSignedPartialMaximal I N (Finset.univ.erase j)
          (finiteProjectionMap I N G f) x := by
  let F := finiteProjectionMap I N G f
  let V := ∑ j, finiteSignedPartialMaximal I N (Finset.univ.erase j) F x
  let T := (Finset.univ : Finset (Fin m)).powerset.erase Finset.univ
  have hV : 0 ≤ V := Finset.sum_nonneg (fun j _ =>
    finiteSignedPartialMaximal_nonneg I N (Finset.univ.erase j) F x)
  have hF := finiteProjectionMap_productStep_closure I N G f hf hs
  have hcard : (T.card : ℝ) ≤ (2 : ℝ) ^ m := by
    have h := Finset.card_le_card
      (Finset.erase_subset Finset.univ
        (Finset.univ : Finset (Fin m)).powerset)
    have hnat : T.card ≤ 2 ^ m := by
      calc
        T.card ≤ (Finset.univ : Finset (Fin m)).powerset.card := h
        _ = 2 ^ m := by simp
    exact_mod_cast hnat
  have hterm (R : ∀ i, Box (Fin (d i))) (hR : R ∈ productDescendants I N)
      (B : Finset (Fin m)) (hB : B ∈ T) :
      (-1 : ℝ) ^ (m + 1 + B.card) * (productAverageMap B R F).1 x ≤ V := by
    have hne : B ≠ Finset.univ := (Finset.mem_erase.mp hB).1
    have hex : ∃ j, j ∉ B := by
      by_contra h
      push Not at h
      exact hne (Finset.eq_univ_of_forall h)
    obtain ⟨j, hj⟩ := hex
    have hBA : B ⊆ Finset.univ.erase j := by
      intro i hi
      exact Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem hi hj, Finset.mem_univ i⟩
    calc
      _ ≤ |(-1 : ℝ) ^ (m + 1 + B.card) * (productAverageMap B R F).1 x| :=
        le_abs_self _
      _ = |(productAverageMap B R F).1 x| := by simp [abs_mul, abs_pow]
      _ ≤ finiteSignedPartialMaximal I N B F x :=
        Finset.le_sup' (fun Q => |(productAverageMap B Q F).1 x|) hR
      _ ≤ finiteSignedPartialMaximal I N (Finset.univ.erase j) F x :=
        finiteSignedPartialMaximal_mono I N F hF.1 hF.2 B _ hBA x hx
      _ ≤ V := Finset.single_le_sum
        (fun k _ => finiteSignedPartialMaximal_nonneg I N (Finset.univ.erase k) F x)
        (Finset.mem_univ j)
  change finiteFamilyMaximal (averagingRectangles I N G) f x ≤ (2 : ℝ) ^ m * V
  by_cases hB : (averagingRectangles I N G).Nonempty
  · rw [finiteFamilyMaximal, dite_eq_left hB]
    apply Finset.sup'_le
    intro R hR
    by_cases hxR : x ∈ productBox R
    · have hRI := averagingRectangles_subset_productDescendants I N G hR
      have hav : (∫ y in productBox R, |f.1 y|) = ∫ y in productBox R, f.1 y := by
        apply setIntegral_congr_fun (measurableSet_productBox R)
        intro y hy
        exact abs_of_nonneg (hpos y (productBox_subset_root_of_mem_productDescendants hRI hy))
      rw [hav]
      rw [← productAverageMap_univ_eq_integral R f x]
      rw [finite_representation I N hd G R hR f hf hs x hxR]
      calc
        _ ≤ ∑ _B ∈ T, V := Finset.sum_le_sum (fun B hBT => hterm R hRI B hBT)
        _ = (T.card : ℝ) * V := by simp
        _ ≤ (2 : ℝ) ^ m * V := mul_le_mul_of_nonneg_right hcard hV
    · rw [Set.indicator_of_notMem hxR]
      exact mul_nonneg (pow_nonneg (by norm_num) _) hV
  · rw [finiteFamilyMaximal, dite_eq_right hB]
    exact mul_nonneg (pow_nonneg (by norm_num) _) hV

end ReyZygmund
