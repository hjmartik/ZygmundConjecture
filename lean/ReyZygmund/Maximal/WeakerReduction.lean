import ReyZygmund.Maximal.WeakerRepresentation
import ReyZygmund.Maximal.PartialReduction
import ReyZygmund.Geometry.ProductLp

/-!
# The union-family norm reduction under weaker containment

The union maximal function is controlled by the signed partial maxima
of the original common projection. The existing partial-coordinate estimates
then give the same dimension-only constant as the averaging-family reduction.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

private theorem weaker_representation_norm
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : ∀ R ∈ G, ∀ J ∈ G,
      (∀ i, R i ≤ J i) → ∃ i, R i = J i)
    (f : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N f.1)
    (hs : ∀ x, x ∉ productBox I → f.1 x = 0)
    (hpos : ∀ x ∈ productBox I, 0 ≤ f.1 x)
    (p : ℝ) (hp : 1 ≤ p) :
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal (G ∪ averagingRectangles I N G) f x) p) (1 / p) ≤
      (2 : ℝ) ^ m * ∑ j,
        Real.rpow (∫ x in productBox I,
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
    (fun x hx => by
      rw [abs_of_nonneg (hM0 x), abs_of_nonneg (mul_nonneg (by positivity) (hS0 x))]
      exact finite_weaker_representation_maximal I N hd G hG hweak f hf hs hpos x hx)
    p (zero_lt_one.trans_le hp)
  have hsum := rootLp_sum_le I N Finset.univ V (fun j _ => hV j) p hp
  rw [rootLp_const_mul I N S hS ((2 : ℝ) ^ m) p (zero_lt_one.trans_le hp),
    abs_of_nonneg (pow_nonneg (by norm_num) m)] at hmono
  have h := hmono.trans (mul_le_mul_of_nonneg_left hsum (pow_nonneg (by norm_num) m))
  simpa only [abs_of_nonneg (hM0 _), abs_of_nonneg (hV0 _ _), M, V, P] using h

private theorem complement_square_leaf
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) :
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
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) (j : Fin m) (p : ℝ) (hp : 0 < p) :
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteSquareFunction I N (Finset.univ.erase j) F x) p) (1 / p) ≤
      Real.rpow (∫ x in productBox I,
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

/-- The paper's weaker-containment proof applies the maximal-to-square reduction
to the union while keeping the original common projection and dimension constant. -/
theorem finite_weaker_maximal_to_square
    (hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : ∀ R ∈ G, ∀ J ∈ G,
      (∀ i, R i ≤ J i) → ∃ i, R i = J i)
    (f : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N f.1)
    (hs : ∀ x, x ∉ productBox I → f.1 x = 0)
    (hpos : ∀ x ∈ productBox I, 0 ≤ f.1 x)
    (p : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 : ℝ) / 2) :
    let C := (m : ℝ) * (2 : ℝ) ^ m *
      ((2 : ℝ) ^ (6 * (∑ i, d i) + 10) + (2 : ℝ) ^ (m - 1))
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal (G ∪ averagingRectangles I N G) f x) p) (1 / p) ≤
      C * (p / (p - 1)) ^ (m - 2) *
        Real.rpow (∫ x in productBox I, Real.rpow |f.1 x| p) (1 / p) +
      C * Real.rpow (∫ x in productBox I,
        Real.rpow (finiteComplementSquareFunction I N (finiteProjectionMap I N G f) x) p)
        (1 / p) := by
  let P := finiteProjectionMap I N G f
  let c : ℝ := (2 : ℝ) ^ (6 * (∑ i, d i) + 10)
  let b : ℝ := (2 : ℝ) ^ (m - 1)
  let a : ℝ := (m : ℝ) * (2 : ℝ) ^ m
  let q : ℝ := (p / (p - 1)) ^ (m - 2)
  let Y := Real.rpow (∫ x in productBox I, Real.rpow |f.1 x| p) (1 / p)
  let W := Real.rpow (∫ x in productBox I,
    Real.rpow (finiteComplementSquareFunction I N P x) p) (1 / p)
  let V := fun j => Real.rpow (∫ x in productBox I,
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
  have hrep := weaker_representation_norm I N hd G hG hweak f hf hs hpos p hp.le
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

end ReyZygmund
