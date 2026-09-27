import ReyZygmund.Weighted.ProjectedRow
import ReyZygmund.Weighted.Product
import ReyZygmund.Geometry.FiniteSquare

/-!
# Summing the projected weighted square estimate

Every row uses the same averaging-family maximal denominator, while
its cross-coordinate partition depends on the other difference indices.
The finite sum and the integrals are interchanged only after integrability
has been derived from the concrete smallest-cube structure.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- The sharper finite estimate, retaining the exact product constant in
each complement of a coordinate. -/
theorem projected_weighted_square_exact
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productBox I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
    let F := finiteInput I N f hf
    (∫ x in productBox I,
      (finiteComplementSquareFunction I N (finiteProjectionMap I N G F) x) ^ 2 /
        Real.rpow (finiteFamilyMaximal (averagingRectangles I N G) F x) (2 - p)) ≤
      (∑ j : Fin m,
        Real.rpow 2 ((2 - p) * ∑ i ∈ Finset.univ.erase j, (d i : ℝ)) *
          ((3 - p) / (p - 1)) ^ (Finset.univ.erase j).card) *
        ∫ x in productBox I, Real.rpow (f x) p := by
  let F := finiteInput I N f hf
  let P := finiteProjectionMap I N G F
  let M := finiteFamilyMaximal (averagingRectangles I N G) F
  let e := fun (j : Fin m) (Q : ∀ i, Box (Fin (d i))) (x : ProductPoint d) =>
    ((productDifferenceMap (Finset.univ.erase j) Q P).1 x) ^ 2 /
      Real.rpow (M x) (2 - p)
  have hF : ProductLeafConstant I N F.1 := productLeafConstant_indicator hf
  have hFs : ∀ x, x ∉ productBox I → F.1 x = 0 :=
    fun x hx => Set.indicator_of_notMem hx f
  have hP := finiteProjectionMap_productStep_closure I N G F hF hFs
  have hM := productLeafConstant_finiteFamilyMaximal I N (averagingRectangles I N G)
    (averagingRectangles_subset_productDescendants I N G) F
  change ProductLeafConstant I N M at hM
  have hei : ∀ j : Fin m, ∀ Q ∈ partialInterior I N (Finset.univ.erase j),
      IntegrableOn (e j Q) (productBox I) volume := by
    intro j Q hQ
    have hdif := (productDifferenceMap_productStep_closure I N P hP.1 hP.2
      (Finset.univ.erase j) Q (fun i hi => partialInterior_mem_selected hQ hi)).1
    apply integrableOn_productLeafConstant I N
    intro R hR x hx y hy
    change ((productDifferenceMap (Finset.univ.erase j) Q P).1 x) ^ 2 /
        Real.rpow (M x) (2 - p) = _
    rw [hdif R hR x hx y hy, hM R hR x hx y hy]
  have heq : (fun x => (finiteComplementSquareFunction I N P x) ^ 2 /
      Real.rpow (M x) (2 - p)) =
      fun x => ∑ j : Fin m, ∑ Q ∈ partialInterior I N (Finset.univ.erase j), e j Q x := by
    funext x
    simp only [finiteComplementSquareFunction_sq, Finset.sum_div, e]
  change (∫ x in productBox I,
      (finiteComplementSquareFunction I N P x) ^ 2 / Real.rpow (M x) (2 - p)) ≤ _
  rw [heq]
  rw [integral_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum _ (fun Q hQ => hei j Q hQ))]
  simp_rw [integral_finsetSum _ (fun Q hQ => hei _ Q hQ)]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  calc
    (∑ Q ∈ partialInterior I N (Finset.univ.erase j),
        ∫ x in productBox I, e j Q x) ≤
      ∑ Q ∈ partialInterior I N (Finset.univ.erase j), ∫ x in productBox I,
        ((productDifferenceMap (Finset.univ.erase j) Q F).1 x) ^ 2 /
          Real.rpow ((productAverageMap (Finset.univ.erase j) Q F).1 x) (2 - p) := by
      apply Finset.sum_le_sum
      intro Q hQ
      exact projected_row_energy I N hd G hG f hf hfpos p hp hp2 j Q
        (fun i hij => partialInterior_mem_selected hQ
          (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩))
    _ ≤ _ := product_weighted_square I N f hf hfpos p hp hp2
      (Finset.univ.erase j) (fun i _ => hd i)

private theorem complement_product_constant_le (j : Fin m)
    (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
    Real.rpow 2 ((2 - p) * ∑ i ∈ Finset.univ.erase j, (d i : ℝ)) *
        ((3 - p) / (p - 1)) ^ (Finset.univ.erase j).card ≤
      (2 : ℝ) ^ ((∑ i, d i) + (m - 1)) / (p - 1) ^ (m - 1) := by
  have hsum : (∑ i ∈ Finset.univ.erase j, (d i : ℝ)) ≤ (∑ i, d i : ℕ) := by
    exact_mod_cast (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset j Finset.univ) (fun _ _ _ => Nat.zero_le _))
  have he : (2 - p) * (∑ i ∈ Finset.univ.erase j, (d i : ℝ)) ≤
      (∑ i, d i : ℕ) := by
    calc
      _ ≤ 1 * (∑ i ∈ Finset.univ.erase j, (d i : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith)
          (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
      _ ≤ _ := by simpa only [one_mul] using hsum
  have hpow : Real.rpow 2 ((2 - p) * ∑ i ∈ Finset.univ.erase j, (d i : ℝ)) ≤
      (2 : ℝ) ^ (∑ i, d i) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_natCast] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he)
  have hratio : (3 - p) / (p - 1) ≤ 2 / (p - 1) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hratio0 : 0 ≤ (3 - p) / (p - 1) := div_nonneg (by linarith) (by linarith)
  have hcard : (Finset.univ.erase j).card = m - 1 := by simp
  rw [hcard]
  calc
    _ ≤ (2 : ℝ) ^ (∑ i, d i) * (2 / (p - 1)) ^ (m - 1) :=
      mul_le_mul hpow (pow_le_pow_left₀ hratio0 hratio _)
        (pow_nonneg hratio0 _) (by positivity)
    _ = _ := by rw [div_pow, ← mul_div_assoc, ← pow_add]

/-- The paper's constant, with every dimension and `p - 1` factor explicit.
No incomparability assumption is needed for this weighted estimate. -/
theorem projected_weighted_square
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productBox I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
    let F := finiteInput I N f hf
    (∫ x in productBox I,
      (finiteComplementSquareFunction I N (finiteProjectionMap I N G F) x) ^ 2 /
        Real.rpow (finiteFamilyMaximal (averagingRectangles I N G) F x) (2 - p)) ≤
      ((m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)) / (p - 1) ^ (m - 1)) *
        ∫ x in productBox I, Real.rpow (f x) p := by
  refine (projected_weighted_square_exact I N hd G hG f hf hfpos p hp hp2).trans ?_
  apply mul_le_mul_of_nonneg_right
  · calc
      _ ≤ ∑ _j : Fin m,
          (2 : ℝ) ^ ((∑ i, d i) + (m - 1)) / (p - 1) ^ (m - 1) :=
        Finset.sum_le_sum (fun j _ => complement_product_constant_le j p hp hp2)
      _ = _ := by simp [mul_div_assoc]
  · exact integral_nonneg_of_ae (ae_restrict_of_forall_mem (measurableSet_productBox I)
      (fun x hx => Real.rpow_nonneg (hfpos x hx).le p))

end ReyZygmund
