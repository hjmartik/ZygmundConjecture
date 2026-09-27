import ReyZygmund.Maximal.WeakerReduction
import ReyZygmund.Maximal.Represented

/-!
# The finite maximal estimate under weaker containment

The projected Hölder estimate retains the averaging-family maximal norm.
Its monotonicity into the union-family norm permits the same scalar absorption
and the same dimension-only constant. The original family is then a subfamily
of this union, with no asserted inclusion in the averaging family.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

private theorem family_norm_mono
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G H : Finset (∀ i, Box (Fin (d i))))
    (hG : G ⊆ productDescendants I N) (hH : H ⊆ productDescendants I N)
    (hGH : G ⊆ H) (F : boundedMeasurableFunctions d) (p : ℝ) (hp : 0 < p) :
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal G F x) p) (1 / p) ≤
      Real.rpow (∫ x in productBox I,
        Real.rpow (finiteFamilyMaximal H F x) p) (1 / p) := by
  have h := rootLp_mono I N (finiteFamilyMaximal G F) (finiteFamilyMaximal H F)
    (productLeafConstant_finiteFamilyMaximal I N G hG F)
    (productLeafConstant_finiteFamilyMaximal I N H hH F)
    (fun x _ => by
      rw [abs_of_nonneg (finiteFamilyMaximal_nonneg G F x),
        abs_of_nonneg (finiteFamilyMaximal_nonneg H F x)]
      exact finiteFamilyMaximal_mono G H hGH F x) p hp
  simpa only [abs_of_nonneg (finiteFamilyMaximal_nonneg _ _ _)] using h

/-- The finite strict-positive union estimate in the paper's weaker-containment
proof. The original projection and `maximalDimensionConstant` are unchanged. -/
theorem finite_weaker_union_maximal_norm
    (hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : ∀ R ∈ G, ∀ J ∈ G,
      (∀ i, R i ≤ J i) → ∃ i, R i = J i)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productBox I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 : ℝ) / 2) :
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal (G ∪ averagingRectangles I N G)
        (finiteInput I N f hf) x) p) (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p) := by
  let F := finiteInput I N f hf
  let B := averagingRectangles I N G
  let H := G ∪ B
  let M := finiteFamilyMaximal H F
  let MB := finiteFamilyMaximal B F
  let W := finiteComplementSquareFunction I N (finiteProjectionMap I N G F)
  let X := Real.rpow (∫ x in productBox I, Real.rpow (M x) p) (1 / p)
  let XB := Real.rpow (∫ x in productBox I, Real.rpow (MB x) p) (1 / p)
  let Y := Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p)
  let Z := Real.rpow (∫ x in productBox I, Real.rpow (W x) p) (1 / p)
  let C₀ : ℝ := (m : ℝ) * (2 : ℝ) ^ m *
    ((2 : ℝ) ^ (6 * (∑ i, d i) + 10) + (2 : ℝ) ^ (m - 1))
  let D := Real.sqrt ((m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)))
  let C := 1 + C₀ * (1 + D)
  let q : ℝ := (p / (p - 1)) ^ (m - 2)
  let s := Real.rpow (p - 1) (-((m - 1 : ℕ) : ℝ) / 2)
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
  have hred := finite_weaker_maximal_to_square hm I N hd G hG hweak F hF hFs hFp p hp hp3
  rw [hYeq] at hred
  change X ≤ C₀ * q * Y + C₀ * Z at hred
  have hholder := projected_holder_norm_variables (by omega : 0 < m)
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
  have hs : 0 ≤ s := Real.rpow_nonneg (sub_pos.mpr hp).le _
  have hX : 0 ≤ X := Real.rpow_nonneg
    (integral_nonneg (fun x => Real.rpow_nonneg (finiteFamilyMaximal_nonneg H F x) p)) _
  have hXB0 : 0 ≤ XB := Real.rpow_nonneg
    (integral_nonneg (fun x => Real.rpow_nonneg (finiteFamilyMaximal_nonneg B F x) p)) _
  have hY : 0 ≤ Y := Real.rpow_nonneg
    (integral_nonneg_of_ae (ae_restrict_of_forall_mem (measurableSet_productBox I)
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
  exact Weighted.weighted_absorption m hm p C X Y hp hp3 hC hX hY hcombined

/-- The original-family finite bound follows from inclusion into the union,
not from inclusion into the averaging family. -/
theorem finite_weaker_maximal_norm
    (hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : ∀ R ∈ G, ∀ J ∈ G,
      (∀ i, R i ≤ J i) → ∃ i, R i = J i)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productBox I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 : ℝ) / 2) :
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal G (finiteInput I N f hf) x) p) (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p) := by
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
    (finite_weaker_union_maximal_norm hm I N hd G hG hweak f hf hfpos p hp hp3)

end ReyZygmund
