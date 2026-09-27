import ReyZygmund.Maximal.Square
import ReyZygmund.Maximal.SignedForest
import ReyZygmund.Geometry.DifferenceForest
import ReyZygmund.Geometry.GridRootExpansion
import ReyZygmund.Geometry.ProductIntegrability

/-! # Uniform finite estimates for the signed square inequality

Place the difference indices and averaging indices inside pairwise disjoint top
rectangles. Choose the smallest scale fine enough to include every child used by a
difference. The constant is independent of these rectangles, scales and averaging
indices.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

theorem finite_signed_grid_square_lintegral
    (D : ∀ i, DyadicGrid (d i)) (hd : ∀ i, 0 < d i)
    (H : Finset (∀ i, Box (Fin (d i)))) (hH : (↑H : Set _) ⊆ gridRectangles D)
    (F : boundedMeasurableFunctions d)
    (hex : F.1 = fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x)
    (A : Finset (∀ i, Box (Fin (d i)))) (hA : (↑A : Set _) ⊆ gridRectangles D)
    (p : ℝ) (hp : 1 ≤ p) (hp3 : p ≤ (3 : ℝ) / 2) :
    (∫⁻ x, (finiteSignedGridMaximal A F.1 x) ^ p) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (6 * (∑ i, d i) + 10)) *
        ENNReal.ofReal (∫ x, Real.rpow (finiteDifferenceSquare H F.1 x) p) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hHA : (↑(H ∪ A) : Set _) ⊆ gridRectangles D := by
    intro Q hQ
    rcases Finset.mem_union.mp hQ with hQ | hQ
    · exact hH hQ
    · exact hA hQ
  obtain ⟨k, N, T, _, hdis, hcover, hcut⟩ := exists_finite_grid_roots D (H ∪ A) hHA
  have hcH : ∀ Q ∈ H, ∃ R ∈ T, ∀ i, Q i ≤ R i :=
    fun Q hQ => hcover Q (Finset.mem_union_left A hQ)
  have hcA : ∀ Q ∈ A, ∃ R ∈ T, ∀ i, Q i ≤ R i :=
    fun Q hQ => hcover Q (Finset.mem_union_right H hQ)
  let HR (R : ∀ i, Box (Fin (d i))) := H.filter (fun Q => ∀ i, Q i ≤ R i)
  let S (R : ∀ i, Box (Fin (d i))) : boundedMeasurableFunctions d :=
    ∑ Q ∈ HR R, productDifferenceMap Finset.univ Q F
  have hHR (R : ∀ i, Box (Fin (d i))) (hR : R ∈ T) :
      HR R ⊆ productInterior R (fun _ => N + 1) := by
    intro Q hQ
    obtain ⟨hQH, hQR⟩ := Finset.mem_filter.mp hQ
    have hdesc := hcut R hR (Finset.mem_filter.mpr ⟨Finset.mem_union_left A hQH, hQR⟩)
    apply Fintype.mem_piFinset.mpr
    intro i
    obtain ⟨n, hn, hlev⟩ := mem_descendants.mp (mem_productDescendants.mp hdesc i)
    exact mem_interior.mpr ⟨n, Nat.lt_succ_of_le hn, hlev⟩
  have hAc (R : ∀ i, Box (Fin (d i))) (hR : R ∈ T) :
      A.filter (fun Q => ∀ i, Q i ≤ R i) ⊆ productDescendants R (fun _ => N + 1) := by
    intro Q hQ
    obtain ⟨hQA, hQR⟩ := Finset.mem_filter.mp hQ
    have hdesc := hcut R hR (Finset.mem_filter.mpr ⟨Finset.mem_union_right H hQA, hQR⟩)
    apply mem_productDescendants.mpr
    intro i
    obtain ⟨n, hn, hlev⟩ := mem_descendants.mp (mem_productDescendants.mp hdesc i)
    exact mem_descendants.mpr ⟨n, hn.trans (Nat.le_succ N), hlev⟩
  have heq (R : ∀ i, Box (Fin (d i))) (hR : R ∈ T) (x : ProductPoint d)
      (hx : x ∈ productBox R) : F.1 x = (S R).1 x := by
    rw [congrFun hex x]
    exact (difference_forest_local_eq T H hdis hcH F R hR x hx).symm
  let C : ℝ := (2 : ℝ) ^ (6 * (∑ i, d i) + 10)
  have hC : 0 ≤ C := by positivity
  have hlocal (R : ∀ i, Box (Fin (d i))) (hR : R ∈ T) :
      (∫⁻ x in productBox R,
        (ENNReal.ofReal (finiteSignedProductMaximal R (fun _ => N + 1) (S R) x)) ^ p) ≤
      ENNReal.ofReal C * ENNReal.ofReal
        (∫ x in productBox R, Real.rpow (finiteDifferenceSquare (HR R) F.1 x) p) := by
    have hstep := finite_difference_sum_productStep R (fun _ => N + 1) (HR R) (hHR R hR) F
    have hrec := finite_difference_sum_reexpansion R (fun _ => N + 1) hd (HR R) (hHR R hR) F
    have hsq (x : ProductPoint d) :
        finiteSquareFunction R (fun _ => N + 1) Finset.univ (S R) x =
          finiteDifferenceSquare (HR R) F.1 x := by
      rw [finite_difference_sum_square_eq R (fun _ => N + 1) hd (HR R) (hHR R hR) F x]
      apply congrArg Real.sqrt
      apply Finset.sum_congr rfl
      intro Q _
      rw [congrFun (rawProductDifference_eq_productDifferenceMap Q F) x]
    have hbound := finite_signed_square_integral R (fun _ => N + 1) hd (S R)
      hstep.1 hstep.2 hrec p hp hp3
    simp_rw [hsq] at hbound
    have hconst := productLeafConstant_finiteSignedProductMaximal R (fun _ => N + 1)
      (S R) hstep.1 hstep.2
    have hi : IntegrableOn (fun x => Real.rpow
        (finiteSignedProductMaximal R (fun _ => N + 1) (S R) x) p) (productBox R) volume := by
      apply integrableOn_productLeafConstant R (fun _ => N + 1)
      intro P hP x hx y hy
      exact congrArg (fun z : ℝ => Real.rpow z p) (hconst P hP x hx y hy)
    calc
      _ = ∫⁻ x in productBox R, ENNReal.ofReal (Real.rpow
          (finiteSignedProductMaximal R (fun _ => N + 1) (S R) x) p) := by
        apply lintegral_congr
        intro x
        exact ENNReal.ofReal_rpow_of_nonneg
          (finiteSignedProductMaximal_nonneg R (fun _ => N + 1) (S R) x) hp0.le
      _ = ENNReal.ofReal (∫ x in productBox R, Real.rpow
          (finiteSignedProductMaximal R (fun _ => N + 1) (S R) x) p) :=
        (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun x =>
          Real.rpow_nonneg (finiteSignedProductMaximal_nonneg R (fun _ => N + 1) (S R) x) p))).symm
      _ ≤ ENNReal.ofReal (C * ∫ x in productBox R,
          Real.rpow (finiteDifferenceSquare (HR R) F.1 x) p) :=
        ENNReal.ofReal_le_ofReal hbound
      _ = _ := ENNReal.ofReal_mul hC
  calc
    _ ≤ ∑ R ∈ T, ∫⁻ x in productBox R,
        (ENNReal.ofReal (finiteSignedProductMaximal R (fun _ => N + 1) (S R) x)) ^ p :=
      lintegral_finiteSignedGridMaximal_forest_le T A hdis hcA (fun _ => N + 1) hAc F.1 S heq p hp0
    _ ≤ ∑ R ∈ T, ENNReal.ofReal C * ENNReal.ofReal
        (∫ x in productBox R, Real.rpow (finiteDifferenceSquare (HR R) F.1 x) p) :=
      Finset.sum_le_sum hlocal
    _ = ENNReal.ofReal C * ENNReal.ofReal
        (∑ R ∈ T, ∫ x in productBox R, Real.rpow (finiteDifferenceSquare (HR R) F.1 x) p) := by
      have hn (R : ∀ i, Box (Fin (d i))) : 0 ≤
          ∫ x in productBox R, Real.rpow (finiteDifferenceSquare (HR R) F.1 x) p :=
        integral_nonneg (fun _ => Real.rpow_nonneg (Real.sqrt_nonneg _) p)
      rw [ENNReal.ofReal_sum_of_nonneg (fun R _ => hn R), Finset.mul_sum]
    _ ≤ _ := mul_le_mul_right (ENNReal.ofReal_le_ofReal
      (difference_square_forest_integral_le T H hdis hcH F.1 p hp0)) _

end ReyZygmund
