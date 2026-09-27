import ReyZygmund.Maximal.Reduction
import ReyZygmund.Weighted.ProjectedHolderNorm
import ReyZygmund.Weighted.Absorption

/-!
# The finite incomparable maximal estimate

The averaging-family norm occurs on both sides of the projected
Hölder estimate. The proved scalar absorption therefore applies with a
constant depending only on the coordinate dimensions. Incomparability is
used only at the final inclusion of the original family.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- The finite maximal estimate's dimension-only constant is uniform in the exponent,
top rectangle, smallest scales, family and input. -/
noncomputable def maximalDimensionConstant (d : Fin m → ℕ) : ℝ :=
  (2 * (1 + ((m : ℝ) * (2 : ℝ) ^ m *
      ((2 : ℝ) ^ (6 * (∑ i, d i) + 10) + (2 : ℝ) ^ (m - 1))) *
    (1 + Real.sqrt ((m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)))))) ^ 2

/-- Absorption for the averaging family. No incomparability premise
is needed before passing from this family back to the original rectangles. -/
theorem finite_averaging_maximal_norm
    (hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productBox I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 : ℝ) / 2) :
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal (averagingRectangles I N G)
        (finiteInput I N f hf) x) p) (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p) := by
  let F := finiteInput I N f hf
  let M := finiteFamilyMaximal (averagingRectangles I N G) F
  let W := finiteComplementSquareFunction I N (finiteProjectionMap I N G F)
  let X := Real.rpow (∫ x in productBox I, Real.rpow (M x) p) (1 / p)
  let Y := Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p)
  let Z := Real.rpow (∫ x in productBox I, Real.rpow (W x) p) (1 / p)
  let C₀ : ℝ := (m : ℝ) * (2 : ℝ) ^ m *
    ((2 : ℝ) ^ (6 * (∑ i, d i) + 10) + (2 : ℝ) ^ (m - 1))
  let D := Real.sqrt ((m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)))
  let C := 1 + C₀ * (1 + D)
  let q : ℝ := (p / (p - 1)) ^ (m - 2)
  let s := Real.rpow (p - 1) (-((m - 1 : ℕ) : ℝ) / 2)
  have hF : ProductLeafConstant I N F.1 := productLeafConstant_indicator hf
  have hFs : ∀ x, x ∉ productBox I → F.1 x = 0 :=
    fun x hx => Set.indicator_of_notMem hx f
  have hFp : ∀ x ∈ productBox I, 0 ≤ F.1 x := by
    intro x hx
    change 0 ≤ (productBox I).indicator f x
    rw [Set.indicator_of_mem hx]
    exact (hfpos x hx).le
  have hYeq : Real.rpow (∫ x in productBox I, Real.rpow |F.1 x| p) (1 / p) = Y := by
    congr 1
    apply setIntegral_congr_fun (measurableSet_productBox I)
    intro x hx
    change Real.rpow |(productBox I).indicator f x| p = Real.rpow (f x) p
    rw [Set.indicator_of_mem hx, abs_of_nonneg (hfpos x hx).le]
  have hred := finite_maximal_to_square hm I N hd G F hF hFs hFp p hp hp3
  rw [hYeq] at hred
  change X ≤ C₀ * q * Y + C₀ * Z at hred
  have hholder := projected_holder_norm_variables (by omega : 0 < m)
    I N hd G hG f hf hfpos p hp (by linarith : p ≤ 2)
  change Z ≤ D * s * Real.rpow Y (p / 2) * Real.rpow X (1 - p / 2) at hholder
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
  have hs : 0 ≤ s := Real.rpow_nonneg (sub_pos.mpr hp).le _
  have hX : 0 ≤ X := Real.rpow_nonneg
    (integral_nonneg (fun x => Real.rpow_nonneg (finiteFamilyMaximal_nonneg _ F x) p)) _
  have hY : 0 ≤ Y := Real.rpow_nonneg
    (integral_nonneg_of_ae (ae_restrict_of_forall_mem (measurableSet_productBox I)
      (fun x hx => Real.rpow_nonneg (hfpos x hx).le p))) _
  have hcombined : X ≤ C * q * Y + C * s * Real.rpow Y (p / 2) *
      Real.rpow X (1 - p / 2) := by
    calc
      X ≤ C₀ * q * Y + C₀ * Z := hred
      _ ≤ C₀ * q * Y + C₀ * (D * s * Real.rpow Y (p / 2) *
          Real.rpow X (1 - p / 2)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hholder hC₀)
      _ = C₀ * q * Y + (C₀ * D) * s * Real.rpow Y (p / 2) *
          Real.rpow X (1 - p / 2) := by ring
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC₀ hq) hY)
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCD hs)
            (Real.rpow_nonneg hY _)) (Real.rpow_nonneg hX _))
  exact Weighted.weighted_absorption m hm p C X Y hp hp3 hC hX hY hcombined

/-- Enlarging the finite collection increases its positive maximal function,
including when the smaller collection is empty. -/
theorem finiteFamilyMaximal_mono
    (G H : Finset (∀ i, Box (Fin (d i)))) (hGH : G ⊆ H)
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) :
    finiteFamilyMaximal G F x ≤ finiteFamilyMaximal H F x := by
  by_cases h : G.Nonempty
  · rw [finiteFamilyMaximal, dite_eq_left h]
    exact Finset.sup'_le _ _ (fun Q hQ =>
      positiveMean_le_finiteFamilyMaximal H F Q (hGH hQ) x)
  · simpa only [finiteFamilyMaximal, dite_eq_right h] using finiteFamilyMaximal_nonneg H F x

/-- The finite maximal estimate for product descendants, with strictly positive finite
input and the full stated range of real exponents.
-/
theorem finite_incomparable_maximal_norm
    (hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productBox I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 : ℝ) / 2) :
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal G (finiteInput I N f hf) x) p) (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p) := by
  let F := finiteInput I N f hf
  have hGB := original_subset_averagingRectangles (by omega : 0 < m) I N G hG hinc
  have hnorm := rootLp_mono I N (finiteFamilyMaximal G F)
    (finiteFamilyMaximal (averagingRectangles I N G) F)
    (productLeafConstant_finiteFamilyMaximal I N G hG F)
    (productLeafConstant_finiteFamilyMaximal I N _
      (averagingRectangles_subset_productDescendants I N G) F)
    (fun x _ => by
      rw [abs_of_nonneg (finiteFamilyMaximal_nonneg G F x),
        abs_of_nonneg (finiteFamilyMaximal_nonneg _ F x)]
      exact finiteFamilyMaximal_mono G _ hGB F x) p (zero_lt_one.trans hp)
  have hnorm' : Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal G F x) p) (1 / p) ≤
      Real.rpow (∫ x in productBox I,
        Real.rpow (finiteFamilyMaximal (averagingRectangles I N G) F x) p) (1 / p) := by
    simpa only [abs_of_nonneg (finiteFamilyMaximal_nonneg _ _ _)] using hnorm
  exact hnorm'.trans (finite_averaging_maximal_norm hm I N hd G hG f hf hfpos p hp hp3)

end ReyZygmund
