import ReyZygmund.Projection.AveragingGeometry
import ReyZygmund.Maximal.PartialSigned
import ReyZygmund.Maximal.PartialReduction
import ReyZygmund.Maximal.Constants
import ReyZygmund.Maximal.Family
import ReyZygmund.Weighted.ProjectedConjugateEstimate
import ReyZygmund.Weighted.MaximalAbsorption

/-!
# The finite weakly incomparable maximal estimate

The proof starts from the signed representation on the enlarged family proved
in `Projection.AveragingGeometry`. Proper coordinate subsets give the pointwise
signed-maximal bound; taking norms and estimating the projected partial maxima
then gives the maximal-to-square reduction. The weighted square estimate retains
the averaging-family denominator until monotonicity into the enlarged family
permits absorption. Finally the original family is a subfamily of the enlargement.

The projected-square coefficient is expressed in terms of `p'` before Hölder.
Absorption first produces the exponent `(m - 1) / p`; its comparison with
`m - 1` is the last step. The finite norm estimate holds for `1 < p ≤ 3/2`,
with a constant depending only on the number and dimensions of the blocks.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection
open MathlibOnly (WeaklyIncomparable)

variable {m : ℕ} {d : Fin m → ℕ}

/-- Take the supremum of the signed
representation and bound each proper coordinate subset by a signed maximum
omitting one coordinate. Average indices include the cutoff leaves. -/
theorem finite_weakly_incomparable_representation_maximal
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : WeaklyIncomparable (G : Set (∀ i, Box (Fin (d i)))))
    (f : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N f.1)
    (hs : ∀ x, x ∉ productRectangle I → f.1 x = 0)
    (hpos : ∀ x ∈ productRectangle I, 0 ≤ f.1 x)
    (x : ProductPoint d) :
    finiteFamilyMaximal (G ∪ averagingRectangles I N G) f x ≤
      (2 : ℝ) ^ m * ∑ j,
        finiteSignedPartialMaximal I N (Finset.univ.erase j)
          (finiteProjectionMap I N G f) x := by
  by_cases hx : x ∈ productRectangle I
  swap
  · have hfamily : G ∪ averagingRectangles I N G ⊆ productDescendants I N :=
      Finset.union_subset hG (averagingRectangles_subset_productDescendants I N G)
    rw [finiteFamilyMaximal_eq_zero_of_notMem_root I N _ hfamily f x hx]
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (Finset.sum_nonneg (fun j _ => finiteSignedPartialMaximal_nonneg I N
        (Finset.univ.erase j) (finiteProjectionMap I N G f) x))
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
    by_cases hxR : x ∈ productRectangle R
    · have hRI := hfamily hR
      have hav : (∫ y in productRectangle R, |f.1 y|) = ∫ y in productRectangle R, f.1 y := by
        apply setIntegral_congr_fun (measurableSet_productRectangle R)
        intro y hy
        exact abs_of_nonneg (hpos y (productRectangle_subset_root_of_mem_productDescendants hRI hy))
      rw [hav]
      rw [← productAverageMap_univ_eq_integral R f x]
      rw [finite_weakly_incomparable_representation I N hd G hG hweak R hR f hf hs x hxR]
      calc
        _ ≤ ∑ _A ∈ T, V := Finset.sum_le_sum (fun A hAT => hterm R hRI A hAT)
        _ = (T.card : ℝ) * V := by simp
        _ ≤ (2 : ℝ) ^ m * V := mul_le_mul_of_nonneg_right hcard hV
    · rw [Set.indicator_of_notMem hxR]
      exact mul_nonneg (pow_nonneg (by norm_num) _) hV
  · rw [finiteFamilyMaximal, dite_eq_right hH]
    exact mul_nonneg (pow_nonneg (by norm_num) _) hV

private theorem representation_norm
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : WeaklyIncomparable (G : Set (∀ i, Box (Fin (d i)))))
    (f : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N f.1)
    (hs : ∀ x, x ∉ productRectangle I → f.1 x = 0)
    (hpos : ∀ x ∈ productRectangle I, 0 ≤ f.1 x)
    (p : ℝ) (hp : 1 ≤ p) :
    Real.rpow (∫ x in productRectangle I,
      Real.rpow (finiteFamilyMaximal (G ∪ averagingRectangles I N G) f x) p) (1 / p) ≤
      (2 : ℝ) ^ m * ∑ j,
        Real.rpow (∫ x in productRectangle I,
          Real.rpow (finiteSignedPartialMaximal I N (Finset.univ.erase j)
            (finiteProjectionMap I N G f) x) p) (1 / p) := by
  let P := finiteProjectionMap I N G f
  let M := finiteFamilyMaximal (G ∪ averagingRectangles I N G) f
  let V := fun j => finiteSignedPartialMaximal I N (Finset.univ.erase j) P
  let S := fun x => ∑ j, V j x
  have hfamily : G ∪ averagingRectangles I N G ⊆ productDescendants I N := by
    intro R hR
    rcases Finset.mem_union.mp hR with hR | hR
    · exact hG hR
    · exact averagingRectangles_subset_productDescendants I N G hR
  have hP := finiteProjectionMap_productStep_closure I N G f hf hs
  have hV (j : Fin m) : ProductLeafConstant I N (V j) :=
    productLeafConstant_finiteSignedPartialMaximal I N (Finset.univ.erase j) P hP.1 hP.2
  have hV0 (j : Fin m) (x : ProductPoint d) : 0 ≤ V j x :=
    finiteSignedPartialMaximal_nonneg I N (Finset.univ.erase j) P x
  have hS : ProductLeafConstant I N S := by
    intro Q hQ x hx y hy
    exact Finset.sum_congr rfl (fun j _ => hV j Q hQ x hx y hy)
  have hS0 (x : ProductPoint d) : 0 ≤ S x := Finset.sum_nonneg (fun j _ => hV0 j x)
  have hM : ProductLeafConstant I N M :=
    productLeafConstant_finiteFamilyMaximal I N (G ∪ averagingRectangles I N G) hfamily f
  have hM0 (x : ProductPoint d) : 0 ≤ M x := finiteFamilyMaximal_nonneg _ f x
  have hscaled : ProductLeafConstant I N (fun x => (2 : ℝ) ^ m * S x) := by
    intro Q hQ x hx y hy
    exact congrArg (fun v => (2 : ℝ) ^ m * v) (hS Q hQ x hx y hy)
  have hmono := rootLp_mono I N M (fun x => (2 : ℝ) ^ m * S x) hM hscaled
    (fun x _ => by
      rw [abs_of_nonneg (hM0 x), abs_of_nonneg (mul_nonneg (by positivity) (hS0 x))]
      exact finite_weakly_incomparable_representation_maximal I N hd G hG hweak f hf hs hpos x)
    p (zero_lt_one.trans_le hp)
  have hsum := rootLp_sum_le I N Finset.univ V (fun j _ => hV j) p hp
  rw [rootLp_const_mul I N S hS ((2 : ℝ) ^ m) p (zero_lt_one.trans_le hp),
    abs_of_nonneg (pow_nonneg (by norm_num) m)] at hmono
  have h := hmono.trans (mul_le_mul_of_nonneg_left hsum (pow_nonneg (by norm_num) m))
  simpa only [abs_of_nonneg (hM0 _), abs_of_nonneg (hV0 _ _), M, V, P] using h

private theorem complement_square_leaf
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productRectangle I → F.1 x = 0) :
    ProductLeafConstant I N (finiteComplementSquareFunction I N F) := by
  intro Q hQ x hx y hy
  simp only [finiteComplementSquareFunction_eq_partial]
  apply congrArg Real.sqrt
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun v : ℝ => v ^ 2)
    (productLeafConstant_finiteSquareFunction I N (Finset.univ.erase j) F hf hs
      Q hQ x hx y hy)

private theorem partial_square_le_complement
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (j : Fin m) (x : ProductPoint d) :
    finiteSquareFunction I N (Finset.univ.erase j) F x ≤
      finiteComplementSquareFunction I N F x := by
  rw [finiteComplementSquareFunction_eq_partial]
  have h := Real.sqrt_le_sqrt
    (Finset.single_le_sum
      (fun k (_ : k ∈ (Finset.univ : Finset (Fin m))) =>
        sq_nonneg (finiteSquareFunction I N (Finset.univ.erase k) F x))
      (Finset.mem_univ j))
  simpa only [Real.sqrt_sq_eq_abs,
    abs_of_nonneg (show 0 ≤ finiteSquareFunction I N (Finset.univ.erase j) F x
      from Real.sqrt_nonneg _)] using h

private theorem partial_square_norm_le_complement
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productRectangle I → F.1 x = 0) (j : Fin m) (p : ℝ) (hp : 0 < p) :
    Real.rpow (∫ x in productRectangle I,
      Real.rpow (finiteSquareFunction I N (Finset.univ.erase j) F x) p) (1 / p) ≤
      Real.rpow (∫ x in productRectangle I,
        Real.rpow (finiteComplementSquareFunction I N F x) p) (1 / p) := by
  have hS0 (x : ProductPoint d) :
      0 ≤ finiteSquareFunction I N (Finset.univ.erase j) F x := Real.sqrt_nonneg _
  have hW0 (x : ProductPoint d) :
      0 ≤ finiteComplementSquareFunction I N F x := Real.sqrt_nonneg _
  have h := rootLp_mono I N
    (finiteSquareFunction I N (Finset.univ.erase j) F)
    (finiteComplementSquareFunction I N F)
    (productLeafConstant_finiteSquareFunction I N (Finset.univ.erase j) F hf hs)
    (complement_square_leaf I N F hf hs)
    (fun x _ => by
      rw [abs_of_nonneg (hS0 x), abs_of_nonneg (hW0 x)]
      exact partial_square_le_complement I N F j x) p hp
  simpa only [abs_of_nonneg (hS0 _), abs_of_nonneg (hW0 _)] using h

/-- Maximal-to-square reduction: the representation of the enlarged family,
combined with the partial-coordinate square estimate and top-average remainder.
The projection is indexed by the original family throughout. -/
theorem finite_weakly_incomparable_maximal_to_square
    (hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : WeaklyIncomparable (G : Set (∀ i, Box (Fin (d i)))))
    (f : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N f.1)
    (hs : ∀ x, x ∉ productRectangle I → f.1 x = 0)
    (hpos : ∀ x ∈ productRectangle I, 0 ≤ f.1 x)
    (p : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 : ℝ) / 2) :
    let C := (m : ℝ) * (2 : ℝ) ^ m *
      ((2 : ℝ) ^ (6 * (∑ i, d i) + 10) + (2 : ℝ) ^ (m - 1))
    Real.rpow (∫ x in productRectangle I,
      Real.rpow (finiteFamilyMaximal (G ∪ averagingRectangles I N G) f x) p) (1 / p) ≤
      C * (p / (p - 1)) ^ (m - 2) *
        Real.rpow (∫ x in productRectangle I, Real.rpow |f.1 x| p) (1 / p) +
      C * Real.rpow (∫ x in productRectangle I,
        Real.rpow (finiteComplementSquareFunction I N (finiteProjectionMap I N G f) x) p)
        (1 / p) := by
  let P := finiteProjectionMap I N G f
  let c : ℝ := (2 : ℝ) ^ (6 * (∑ i, d i) + 10)
  let b : ℝ := (2 : ℝ) ^ (m - 1)
  let a : ℝ := (m : ℝ) * (2 : ℝ) ^ m
  let q : ℝ := (p / (p - 1)) ^ (m - 2)
  let Y := Real.rpow (∫ x in productRectangle I, Real.rpow |f.1 x| p) (1 / p)
  let W := Real.rpow (∫ x in productRectangle I,
    Real.rpow (finiteComplementSquareFunction I N P x) p) (1 / p)
  let V := fun j => Real.rpow (∫ x in productRectangle I,
    Real.rpow (finiteSignedPartialMaximal I N (Finset.univ.erase j) P x) p) (1 / p)
  have hP := finiteProjectionMap_productStep_closure I N G f hf hs
  have hc : 0 ≤ c := by positivity
  have hb : 0 ≤ b := by positivity
  have ha : 0 ≤ a := by positivity
  have hq : 0 ≤ q := by
    exact pow_nonneg (div_nonneg (zero_le_one.trans hp.le) (sub_pos.mpr hp).le) _
  have hY : 0 ≤ Y := Real.rpow_nonneg
    (integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) p)) _
  have hW : 0 ≤ W := Real.rpow_nonneg
    (integral_nonneg (fun x => Real.rpow_nonneg (Real.sqrt_nonneg _) p)) _
  have hv (j : Fin m) : V j ≤ c * W + (b - 1) * q * Y := by
    have h := finite_projected_partial_maximal_norm hm I N hd G f hf hs j p hp hp3
    exact h.trans (add_le_add
      (mul_le_mul_of_nonneg_left
        (partial_square_norm_le_complement I N P hP.1 hP.2 j p
          (zero_lt_one.trans hp)) hc) le_rfl)
  have hrep := representation_norm I N hd G hG hweak f hf hs hpos p hp.le
  change _ ≤ (a * (c + b)) * q * Y + (a * (c + b)) * W
  calc
    _ ≤ (2 : ℝ) ^ m * ∑ j, V j := hrep
    _ ≤ (2 : ℝ) ^ m * ∑ _j : Fin m, (c * W + (b - 1) * q * Y) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hv j)) (by positivity)
    _ = (a * (b - 1)) * q * Y + (a * c) * W := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, a]
      ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith : b - 1 ≤ c + b) ha) hq) hY)
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hb) ha) hW)

private theorem family_norm_mono
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G H : Finset (∀ i, Box (Fin (d i))))
    (hG : G ⊆ productDescendants I N) (hH : H ⊆ productDescendants I N)
    (hGH : G ⊆ H) (F : boundedMeasurableFunctions d) (p : ℝ) (hp : 0 < p) :
    Real.rpow (∫ x in productRectangle I,
      Real.rpow (finiteFamilyMaximal G F x) p) (1 / p) ≤
      Real.rpow (∫ x in productRectangle I,
        Real.rpow (finiteFamilyMaximal H F x) p) (1 / p) := by
  have h := rootLp_mono I N (finiteFamilyMaximal G F) (finiteFamilyMaximal H F)
    (productLeafConstant_finiteFamilyMaximal I N G hG F)
    (productLeafConstant_finiteFamilyMaximal I N H hH F)
    (fun x _ => by
      rw [abs_of_nonneg (finiteFamilyMaximal_nonneg G F x),
        abs_of_nonneg (finiteFamilyMaximal_nonneg H F x)]
      exact finiteFamilyMaximal_mono G H hGH F x) p hp
  simpa only [abs_of_nonneg (finiteFamilyMaximal_nonneg _ _ _)] using h

/-- The maximal estimate for the union with the averaging family.
First apply the maximal-to-square reduction; then retain the averaging
maximal function in the weighted estimate, dominate it by the union maximum,
and apply scalar absorption. -/
theorem finite_weakly_incomparable_union_maximal_norm
    (hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : WeaklyIncomparable (G : Set (∀ i, Box (Fin (d i)))))
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productRectangle I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 : ℝ) / 2) :
    Real.rpow (∫ x in productRectangle I,
      Real.rpow (finiteFamilyMaximal (G ∪ averagingRectangles I N G)
        (finiteInput I N f hf) x) p) (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productRectangle I, Real.rpow (f x) p) (1 / p) := by
  let F := finiteInput I N f hf
  let B := averagingRectangles I N G
  let H := G ∪ B
  let M := finiteFamilyMaximal H F
  let MB := finiteFamilyMaximal B F
  let W := finiteComplementSquareFunction I N (finiteProjectionMap I N G F)
  let X := Real.rpow (∫ x in productRectangle I, Real.rpow (M x) p) (1 / p)
  let XB := Real.rpow (∫ x in productRectangle I, Real.rpow (MB x) p) (1 / p)
  let Y := Real.rpow (∫ x in productRectangle I, Real.rpow (f x) p) (1 / p)
  let Z := Real.rpow (∫ x in productRectangle I, Real.rpow (W x) p) (1 / p)
  let C₀ : ℝ := (m : ℝ) * (2 : ℝ) ^ m *
    ((2 : ℝ) ^ (6 * (∑ i, d i) + 10) + (2 : ℝ) ^ (m - 1))
  let D := Real.sqrt ((m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)))
  let C := 1 + C₀ * (1 + D)
  let q : ℝ := (p / (p - 1)) ^ (m - 2)
  let s := Real.rpow (p / (p - 1)) (((m - 1 : ℕ) : ℝ) / 2)
  have hB : B ⊆ productDescendants I N :=
    averagingRectangles_subset_productDescendants I N G
  have hH : H ⊆ productDescendants I N := by
    intro R hR
    rcases Finset.mem_union.mp hR with hR | hR
    · exact hG hR
    · exact hB hR
  have hBH : B ⊆ H := by
    intro R hR
    exact Finset.mem_union_right G hR
  have hXB : XB ≤ X :=
    family_norm_mono I N B H hB hH hBH F p (zero_lt_one.trans hp)
  have hF : ProductLeafConstant I N F.1 := productLeafConstant_indicator hf
  have hFs : ∀ x, x ∉ productRectangle I → F.1 x = 0 :=
    fun x hx => Set.indicator_of_notMem hx f
  have hFp : ∀ x ∈ productRectangle I, 0 ≤ F.1 x := by
    intro x hx
    change 0 ≤ (productRectangle I).indicator f x
    rw [Set.indicator_of_mem hx]
    exact (hfpos x hx).le
  have hYeq : Real.rpow (∫ x in productRectangle I, Real.rpow |F.1 x| p) (1 / p) = Y := by
    congr 1
    apply setIntegral_congr_fun (measurableSet_productRectangle I)
    intro x hx
    change Real.rpow |(productRectangle I).indicator f x| p = Real.rpow (f x) p
    rw [Set.indicator_of_mem hx, abs_of_nonneg (hfpos x hx).le]
  have hred := finite_weakly_incomparable_maximal_to_square hm I N hd G hG hweak F hF hFs hFp p hp hp3
  rw [hYeq] at hred
  change X ≤ C₀ * q * Y + C₀ * Z at hred
  have hholder := projected_holder_norm_variables_conjugate (by omega : 0 < m)
    I N hd G hG f hf hfpos p hp (by linarith : p ≤ 2)
  change Z ≤ D * s * Real.rpow Y (p / 2) * Real.rpow XB (1 - p / 2) at hholder
  have hC₀ : 0 ≤ C₀ := by positivity
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hC : 1 ≤ C := le_add_of_nonneg_right
    (mul_nonneg hC₀ (add_nonneg zero_le_one hD))
  have hCC₀ : C₀ ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg hC₀ hD]
  have hCD : C₀ * D ≤ C := by dsimp only [C]; nlinarith
  have hq : 0 ≤ q :=
    pow_nonneg (div_nonneg (zero_le_one.trans hp.le) (sub_pos.mpr hp).le) _
  have hs : 0 ≤ s := Real.rpow_nonneg
    (div_nonneg (zero_lt_one.trans hp).le (sub_pos.mpr hp).le) _
  have hX : 0 ≤ X := Real.rpow_nonneg
    (integral_nonneg (fun x => Real.rpow_nonneg (finiteFamilyMaximal_nonneg H F x) p)) _
  have hXB0 : 0 ≤ XB := Real.rpow_nonneg
    (integral_nonneg (fun x => Real.rpow_nonneg (finiteFamilyMaximal_nonneg B F x) p)) _
  have hY : 0 ≤ Y := Real.rpow_nonneg
    (integral_nonneg_of_ae (ae_restrict_of_forall_mem (measurableSet_productRectangle I)
      (fun x hx => Real.rpow_nonneg (hfpos x hx).le p))) _
  have hholder_union : Z ≤ D * s * Real.rpow Y (p / 2) *
      Real.rpow X (1 - p / 2) := by
    exact hholder.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hXB0 hXB (by linarith : 0 ≤ 1 - p / 2))
      (mul_nonneg (mul_nonneg hD hs) (Real.rpow_nonneg hY _)))
  have hcombined : X ≤ C * q * Y + C * s * Real.rpow Y (p / 2) *
      Real.rpow X (1 - p / 2) := by
    calc
      X ≤ C₀ * q * Y + C₀ * Z := hred
      _ ≤ C₀ * q * Y + C₀ * (D * s * Real.rpow Y (p / 2) *
          Real.rpow X (1 - p / 2)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hholder_union hC₀)
      _ = C₀ * q * Y + (C₀ * D) * s * Real.rpow Y (p / 2) *
          Real.rpow X (1 - p / 2) := by ring
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC₀ hq) hY)
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCD hs)
            (Real.rpow_nonneg hY _)) (Real.rpow_nonneg hX _))
  exact Weighted.weighted_absorption_conjugate m hm p C X Y hp hp3 hC hX hY hcombined

/-- The weakly incomparable maximal estimate in the finite
descendant model. Inclusion in the enlarged family finishes the proof. -/
theorem finite_weakly_incomparable_maximal_norm
    (hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : WeaklyIncomparable (G : Set (∀ i, Box (Fin (d i)))))
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productRectangle I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 : ℝ) / 2) :
    Real.rpow (∫ x in productRectangle I,
      Real.rpow (finiteFamilyMaximal G (finiteInput I N f hf) x) p) (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productRectangle I, Real.rpow (f x) p) (1 / p) := by
  have hH : G ∪ averagingRectangles I N G ⊆ productDescendants I N := by
    intro R hR
    rcases Finset.mem_union.mp hR with hR | hR
    · exact hG hR
    · exact averagingRectangles_subset_productDescendants I N G hR
  have hGH : G ⊆ G ∪ averagingRectangles I N G := by
    intro R hR
    exact Finset.mem_union_left _ hR
  have hnorm := family_norm_mono I N G (G ∪ averagingRectangles I N G) hG hH hGH
    (finiteInput I N f hf) p (zero_lt_one.trans hp)
  exact hnorm.trans
    (finite_weakly_incomparable_union_maximal_norm hm I N hd G hG hweak f hf hfpos p hp hp3)

end ReyZygmund
