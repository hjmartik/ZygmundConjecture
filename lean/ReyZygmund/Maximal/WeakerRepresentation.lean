import ReyZygmund.Maximal.RepresentationBound

/-!
# Representation under the weaker containment condition

The original and averaging rectangles use the same common projection. A full
interior difference below an original rectangle is removed by definition; the
weaker containment condition preserves that rectangle's average. The signed
representation therefore holds on the union, without assuming that the
original family is contained in the averaging family.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- Preservation of averages under weaker containment and the representation on the union
family. The projection is defined from the original family, and the input is signed. -/
theorem Projection.finite_weaker_representation
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : ∀ R ∈ G, ∀ J ∈ G,
      (∀ i, R i ≤ J i) → ∃ i, R i = J i)
    (R : ∀ i, Box (Fin (d i)))
    (hR : R ∈ G ∪ averagingRectangles I N G)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (x : ProductPoint d) (hx : x ∈ productBox R) :
    (productAverageMap Finset.univ R F).1 x =
      ∑ A ∈ ((Finset.univ : Finset (Fin m)).powerset.erase Finset.univ),
        (-1 : ℝ) ^ (m + 1 + A.card) *
          (productAverageMap A R (finiteProjectionMap I N G F)).1 x := by
  rcases Finset.mem_union.mp hR with hR | hR
  · let FP := finiteProjectionMap I N G F
    have hc := finiteProjectionMap_productStep_closure I N G F hf hs
    have hzero :
        (∑ L ∈ (productInterior I N).filter (fun L => ∀ i, L i ≤ R i),
          (productDifferenceMap Finset.univ L FP).1 x) = 0 := by
      apply Finset.sum_eq_zero
      intro L hL
      obtain ⟨hLi, hLR⟩ := Finset.mem_filter.mp hL
      have hremoved : L ∈ removedIndices I N G :=
        Finset.mem_filter.mpr ⟨hLi, R, hR, hLR⟩
      have h := congrArg
        (fun T : Module.End ℝ (boundedMeasurableFunctions d) => (T F).1 x)
        (productDifferenceMap_mul_finiteProjectionMap I N hd G L hremoved)
      simpa [FP, Module.End.mul_apply] using h
    have hexp := local_product_expansion I N hd R (mem_productDescendants.mp (hG hR))
      FP hc.1 hc.2 x hx
    have hfull :
        (∑ A ∈ (Finset.univ : Finset (Fin m)).powerset,
          (-1 : ℝ) ^ A.card * (productAverageMap A R FP).1 x) = 0 :=
      hexp.symm.trans hzero
    let S := ∑ A ∈ ((Finset.univ : Finset (Fin m)).powerset.erase Finset.univ),
      (-1 : ℝ) ^ A.card * (productAverageMap A R FP).1 x
    have hsplit : (-1 : ℝ) ^ m * (productAverageMap Finset.univ R FP).1 x + S = 0 := by
      have h := (Finset.add_sum_erase (Finset.univ : Finset (Fin m)).powerset
        (fun A => (-1 : ℝ) ^ A.card * (productAverageMap A R FP).1 x)
        (by simp : (Finset.univ : Finset (Fin m)) ∈ Finset.univ.powerset)).trans hfull
      simpa only [Finset.card_univ, Fintype.card_fin, S] using h
    have hval : (-1 : ℝ) ^ m * (productAverageMap Finset.univ R FP).1 x = -S := by
      linarith
    have hsign : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    have hstrict : ∀ Q ∈ G, ∀ J ∈ G, ¬ ∀ i, Q i < J i := by
      intro Q hQ J hJ hlt
      obtain ⟨i, hi⟩ := hweak Q hQ J hJ (fun i => (hlt i).le)
      exact (ne_of_lt (hlt i)) hi
    have hpres : (productAverageMap Finset.univ R FP).1 x =
        (productAverageMap Finset.univ R F).1 x := by
      exact congrArg
        (fun T : Module.End ℝ (boundedMeasurableFunctions d) => (T F).1 x)
        (original_averages_preserved_of_weaker_containment I N hd G hG hstrict R hR)
    rw [← hpres]
    calc
      _ = ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) *
          (productAverageMap Finset.univ R FP).1 x := by rw [hsign, one_mul]
      _ = (-1 : ℝ) ^ m *
          ((-1 : ℝ) ^ m * (productAverageMap Finset.univ R FP).1 x) := by ring
      _ = -((-1 : ℝ) ^ m) * S := by rw [hval]; ring
      _ = ∑ A ∈ ((Finset.univ : Finset (Fin m)).powerset.erase Finset.univ),
          -((-1 : ℝ) ^ m) *
            ((-1 : ℝ) ^ A.card * (productAverageMap A R FP).1 x) := by
        exact Finset.mul_sum _ _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro A _
        simp only [pow_add, pow_one]
        ring
  · exact finite_representation I N hd G R hR F hf hs x hx

/-- The union maximal function has the same pointwise `2^m` bound. Taking a
finite supremum does not add the separate original and averaging bounds. -/
theorem finite_weaker_representation_maximal
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : ∀ R ∈ G, ∀ J ∈ G,
      (∀ i, R i ≤ J i) → ∃ i, R i = J i)
    (f : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N f.1)
    (hs : ∀ x, x ∉ productBox I → f.1 x = 0)
    (hpos : ∀ x ∈ productBox I, 0 ≤ f.1 x)
    (x : ProductPoint d) (hx : x ∈ productBox I) :
    finiteFamilyMaximal (G ∪ averagingRectangles I N G) f x ≤
      (2 : ℝ) ^ m * ∑ j,
        finiteSignedPartialMaximal I N (Finset.univ.erase j)
          (finiteProjectionMap I N G f) x := by
  let F := finiteProjectionMap I N G f
  let V := ∑ j, finiteSignedPartialMaximal I N (Finset.univ.erase j) F x
  let T := (Finset.univ : Finset (Fin m)).powerset.erase Finset.univ
  have hV : 0 ≤ V := Finset.sum_nonneg (fun j _ =>
    finiteSignedPartialMaximal_nonneg I N (Finset.univ.erase j) F x)
  have hF := finiteProjectionMap_productStep_closure I N G f hf hs
  have hfamily : G ∪ averagingRectangles I N G ⊆ productDescendants I N := by
    intro R hR
    rcases Finset.mem_union.mp hR with hR | hR
    · exact hG hR
    · exact averagingRectangles_subset_productDescendants I N G hR
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
      (A : Finset (Fin m)) (hA : A ∈ T) :
      (-1 : ℝ) ^ (m + 1 + A.card) * (productAverageMap A R F).1 x ≤ V := by
    have hne : A ≠ Finset.univ := (Finset.mem_erase.mp hA).1
    have hex : ∃ j, j ∉ A := by
      by_contra h
      push Not at h
      exact hne (Finset.eq_univ_of_forall h)
    obtain ⟨j, hj⟩ := hex
    have hAj : A ⊆ Finset.univ.erase j := by
      intro i hi
      exact Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem hi hj, Finset.mem_univ i⟩
    calc
      _ ≤ |(-1 : ℝ) ^ (m + 1 + A.card) * (productAverageMap A R F).1 x| :=
        le_abs_self _
      _ = |(productAverageMap A R F).1 x| := by simp [abs_mul, abs_pow]
      _ ≤ finiteSignedPartialMaximal I N A F x :=
        Finset.le_sup' (fun Q => |(productAverageMap A Q F).1 x|) hR
      _ ≤ finiteSignedPartialMaximal I N (Finset.univ.erase j) F x :=
        finiteSignedPartialMaximal_mono I N F hF.1 hF.2 A _ hAj x hx
      _ ≤ V := Finset.single_le_sum
        (fun k _ => finiteSignedPartialMaximal_nonneg I N (Finset.univ.erase k) F x)
        (Finset.mem_univ j)
  change finiteFamilyMaximal (G ∪ averagingRectangles I N G) f x ≤ (2 : ℝ) ^ m * V
  by_cases hH : (G ∪ averagingRectangles I N G).Nonempty
  · rw [finiteFamilyMaximal, dite_eq_left hH]
    apply Finset.sup'_le
    intro R hR
    by_cases hxR : x ∈ productBox R
    · have hRI := hfamily hR
      have hav : (∫ y in productBox R, |f.1 y|) = ∫ y in productBox R, f.1 y := by
        apply setIntegral_congr_fun (measurableSet_productBox R)
        intro y hy
        exact abs_of_nonneg (hpos y (productBox_subset_root_of_mem_productDescendants hRI hy))
      rw [hav]
      rw [← productAverageMap_univ_eq_integral R f x]
      rw [finite_weaker_representation I N hd G hG hweak R hR f hf hs x hxR]
      calc
        _ ≤ ∑ _A ∈ T, V := Finset.sum_le_sum (fun A hAT => hterm R hRI A hAT)
        _ = (T.card : ℝ) * V := by simp
        _ ≤ (2 : ℝ) ^ m * V := mul_le_mul_of_nonneg_right hcard hV
    · rw [Set.indicator_of_notMem hxR]
      exact mul_nonneg (pow_nonneg (by norm_num) _) hV
  · rw [finiteFamilyMaximal, dite_eq_right hH]
    exact mul_nonneg (pow_nonneg (by norm_num) _) hV

end ReyZygmund
