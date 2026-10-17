import ReyZygmund.Maximal.Constants
import ReyZygmund.Maximal.Reduction
import ReyZygmund.Weighted.ProjectedHolderNorm
import ReyZygmund.Weighted.Absorption

/-!
# The maximal estimate for the averaging family

The averaging-family norm occurs on both sides of the projected Hölder estimate.
Scalar absorption therefore applies with a constant depending only on the
coordinate dimensions.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- The maximal norm bound for the averaging family, obtained by scalar absorption. -/
theorem finite_averaging_maximal_norm
    (hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productRectangle I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 : ℝ) / 2) :
    Real.rpow (∫ x in productRectangle I,
      Real.rpow (finiteFamilyMaximal (averagingRectangles I N G)
        (finiteInput I N f hf) x) p) (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productRectangle I, Real.rpow (f x) p) (1 / p) := by
  let F := finiteInput I N f hf
  let M := finiteFamilyMaximal (averagingRectangles I N G) F
  let W := finiteComplementSquareFunction I N (finiteProjectionMap I N G F)
  let X := Real.rpow (∫ x in productRectangle I, Real.rpow (M x) p) (1 / p)
  let Y := Real.rpow (∫ x in productRectangle I, Real.rpow (f x) p) (1 / p)
  let Z := Real.rpow (∫ x in productRectangle I, Real.rpow (W x) p) (1 / p)
  let C₀ : ℝ := (m : ℝ) * (2 : ℝ) ^ m *
    ((2 : ℝ) ^ (6 * (∑ i, d i) + 10) + (2 : ℝ) ^ (m - 1))
  let D := Real.sqrt ((m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)))
  let C := 1 + C₀ * (1 + D)
  let q : ℝ := (p / (p - 1)) ^ (m - 2)
  let s := Real.rpow (p - 1) (-((m - 1 : ℕ) : ℝ) / 2)
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
    (integral_nonneg_of_ae (ae_restrict_of_forall_mem (measurableSet_productRectangle I)
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

end ReyZygmund
