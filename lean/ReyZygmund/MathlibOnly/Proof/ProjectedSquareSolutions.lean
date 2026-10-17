import ReyZygmund.MathlibOnly.SupportingStatements
import ReyZygmund.Geometry.PartialSquareFiniteSetting
import ReyZygmund.Geometry.ProductLp
import ReyZygmund.Maximal.ProductFiniteSetting
import ReyZygmund.Projection.AveragingFiniteSetting
import ReyZygmund.Maximal.WeaklyIncomparableFinite
import ReyZygmund.Weighted.ProjectedConjugateEstimate

/-! # Maximal reduction and the projected square-function estimate

The common smallest scale identifies the finite grid with the subdivisions
used by the coordinate operators. The maximal reduction uses the representation
of averages, the partial square estimate and the top-average remainder.
The projected square estimate combines cross averaging with the product
weighted estimate, using the maximal function of the averaging family
in the denominator.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.MathlibOnly

open Geometry

/-- The enlarged-family maximal function is bounded by the input and projected
square-function norms. -/
theorem maximal_square_function_reduction : MaximalSquareFunctionReduction := by
  intro m totalDim hm
  let C : ℝ := (m : ℝ) * (2 : ℝ) ^ m *
    ((2 : ℝ) ^ (6 * totalDim + 10) + (2 : ℝ) ^ (m - 1))
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro d hd hdim D I k htop f hs hfpos hf G hG hweak p hp hp3
  choose l hI hcut using htop
  let N := fun i => (l i + k).toNat
  have hfl : ProductLeafConstant I N f :=
    (constantOnBottomRectangles_iff D hI hcut f).mp hf
  let u := finiteInput I N f hfl
  have hu : u.1 = f := finiteInput_eq I N f hfl hs
  have hul : ProductLeafConstant I N u.1 := by rw [hu]; exact hfl
  have hus : ∀ x ∉ productRectangle I, u.1 x = 0 := by rw [hu]; exact hs
  have hup : ∀ x ∈ productRectangle I, 0 ≤ u.1 x := by
    rw [hu]; exact fun x hx => (hfpos x hx).le
  let Gfin := (Projection.finite_of_subset_finiteRectangles D hd hI hcut hG).toFinset
  have hGfin : (Gfin : Set (Rectangle d)) = G := Set.Finite.coe_toFinset _
  have hdesc : Gfin ⊆ Projection.productDescendants I N := by
    intro R hR
    have h := hG (by simpa only [← hGfin, Finset.mem_coe] using hR)
    rwa [Projection.finiteRectangles_eq_productDescendants D hd hI hcut] at h
  let B := Projection.averagingRectangles I N Gfin
  let H := Gfin ∪ B
  let P := Projection.finiteProjectionMap I N Gfin u
  let M := ReyZygmund.finiteFamilyMaximal H u
  let W := finiteComplementSquareFunction I N P
  let μ := volume.restrict (productRectangle I)
  have hB : averagingRectangles D I k G = (B : Set (Rectangle d)) := by
    rw [← hGfin]
    exact Projection.averagingRectangles_eq_finiteAveragingRectangles D hd hI hcut Gfin
  have hH : G ∪ averagingRectangles D I k G = (H : Set (Rectangle d)) := by
    rw [hB, ← hGfin, Finset.coe_union]
  have hP : projection D I k G f = P.1 := by
    rw [← hGfin, ← hu]
    exact Projection.projection_eq_finiteProjectionMap D hd hI hcut Gfin u
  have hmax : productMaximal (G ∪ averagingRectangles D I k G) f =
      fun x => ENNReal.ofReal (M x) := by
    rw [hH, ← hu]
    exact ReyZygmund.productMaximal_eq_ofReal_finiteFamilyMaximal H u
  have hW : combinedSquareFunction D I k (projection D I k G f) =
      fun x => ENNReal.ofReal (W x) := by
    rw [hP]
    funext x
    exact combinedSquareFunction_eq_ofReal D hI hcut hd P x
  have hHdesc : H ⊆ Projection.productDescendants I N :=
    Finset.union_subset hdesc (Projection.averagingRectangles_subset_productDescendants I N Gfin)
  have hMleaf : ProductLeafConstant I N M :=
    ReyZygmund.productLeafConstant_finiteFamilyMaximal I N H hHdesc u
  have hPstep := Projection.finiteProjectionMap_productStep_closure I N Gfin u hul hus
  have hWleaf : ProductLeafConstant I N W :=
    productLeafConstant_finiteComplementSquareFunction I N P hPstep.1 hPstep.2
  have hM0 (x) : 0 ≤ M x := ReyZygmund.finiteFamilyMaximal_nonneg H u x
  have hW0 (x) : 0 ≤ W x := Real.sqrt_nonneg _
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hraw := ReyZygmund.finite_weakly_incomparable_maximal_to_square hm I N hd
    Gfin hdesc (by simpa only [hGfin] using hweak) u hul hus hup p hp hp3
  have hreal : lpNorm M (ENNReal.ofReal p) μ ≤
      (C * (p / (p - 1)) ^ (m - 2)) * lpNorm f (ENNReal.ofReal p) μ +
        C * lpNorm W (ENNReal.ofReal p) μ := by
    rw [lpNorm_productLeafConstant_eq I N M hMleaf p hp0,
      lpNorm_productLeafConstant_eq I N f hfl p hp0,
      lpNorm_productLeafConstant_eq I N W hWleaf p hp0]
    simpa only [hu, hdim, abs_of_nonneg (hM0 _), abs_of_nonneg (hW0 _)] using hraw
  have hCq : 0 ≤ C * (p / (p - 1)) ^ (m - 2) :=
    mul_nonneg hC.le (pow_nonneg (div_nonneg hp0.le (sub_pos.mpr hp).le) _)
  have hnorm : eLpNorm M (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (C * (p / (p - 1)) ^ (m - 2)) * eLpNorm f (ENNReal.ofReal p) μ +
        ENNReal.ofReal C * eLpNorm W (ENNReal.ofReal p) μ := by
    rw [← ofReal_lpNorm (memLp_productLeafConstant I N M hMleaf p hp0),
      ← ofReal_lpNorm (memLp_productLeafConstant I N f hfl p hp0),
      ← ofReal_lpNorm (memLp_productLeafConstant I N W hWleaf p hp0)]
    calc
      _ ≤ ENNReal.ofReal ((C * (p / (p - 1)) ^ (m - 2)) *
          lpNorm f (ENNReal.ofReal p) μ + C * lpNorm W (ENNReal.ofReal p) μ) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
        rw [ENNReal.ofReal_add (mul_nonneg hCq lpNorm_nonneg)
          (mul_nonneg hC.le lpNorm_nonneg)]
        exact congrArg₂ (fun a b : ℝ≥0∞ => a + b)
          (ENNReal.ofReal_mul hCq) (ENNReal.ofReal_mul hC.le)
  have hMs : (productRectangle I).indicator M = M := by
    funext x
    by_cases hx : x ∈ productRectangle I
    · exact Set.indicator_of_mem hx M
    · rw [Set.indicator_of_notMem hx]
      exact (ReyZygmund.finiteFamilyMaximal_eq_zero_of_notMem_root I N H hHdesc u x hx).symm
  have hMnorm : eLpNorm M (ENNReal.ofReal p) volume = eLpNorm M (ENNReal.ofReal p) μ := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict
      (measurableSet_productRectangle I).nullMeasurableSet, hMs]
  change eLpNorm (productMaximal (G ∪ averagingRectangles D I k G) f)
      (ENNReal.ofReal p) volume ≤ _
  have hMn : eLpNorm (fun x => ENNReal.ofReal (M x)) (ENNReal.ofReal p) volume =
      eLpNorm M (ENNReal.ofReal p) volume :=
    eLpNorm_ofReal M (Filter.Eventually.of_forall hM0)
  have hWn : eLpNorm (fun x => ENNReal.ofReal (W x)) (ENNReal.ofReal p) volume =
      eLpNorm W (ENNReal.ofReal p) volume :=
    eLpNorm_ofReal W (Filter.Eventually.of_forall hW0)
  rw [hmax, hW, hMn, hWn, hMnorm]
  exact hnorm.trans (add_le_add
    (mul_le_mul' le_rfl (eLpNorm_restrict_le f (ENNReal.ofReal p) volume (productRectangle I)))
    (mul_le_mul' le_rfl (eLpNorm_restrict_le W (ENNReal.ofReal p) volume (productRectangle I))))

/-- The projected weighted square estimate, with the averaging-family maximal
function in the denominator. -/
theorem projected_square_function_estimate : ProjectedSquareFunctionEstimate := by
  intro m totalDim hm
  let C : ℝ := (m : ℝ) * (2 : ℝ) ^ (totalDim + (m - 1))
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro d hd hdim D I k htop f hs hfpos hf G hG p hp hp2
  choose l hI hcut using htop
  let N := fun i => (l i + k).toNat
  have hfl : ProductLeafConstant I N f :=
    (constantOnBottomRectangles_iff D hI hcut f).mp hf
  let u := finiteInput I N f hfl
  have hu : u.1 = f := finiteInput_eq I N f hfl hs
  have hul : ProductLeafConstant I N u.1 := by rw [hu]; exact hfl
  have hus : ∀ x ∉ productRectangle I, u.1 x = 0 := by rw [hu]; exact hs
  have hup : ∀ x ∈ productRectangle I, 0 < u.1 x := by rw [hu]; exact hfpos
  let Gfin := (Projection.finite_of_subset_finiteRectangles D hd hI hcut hG).toFinset
  have hGfin : (Gfin : Set (Rectangle d)) = G := Set.Finite.coe_toFinset _
  have hdesc : Gfin ⊆ Projection.productDescendants I N := by
    intro R hR
    have h := hG (by simpa only [← hGfin, Finset.mem_coe] using hR)
    rwa [Projection.finiteRectangles_eq_productDescendants D hd hI hcut] at h
  let B := Projection.averagingRectangles I N Gfin
  let P := Projection.finiteProjectionMap I N Gfin u
  let M := ReyZygmund.finiteFamilyMaximal B u
  let W := finiteComplementSquareFunction I N P
  have hB : averagingRectangles D I k G = (B : Set (Rectangle d)) := by
    rw [← hGfin]
    exact Projection.averagingRectangles_eq_finiteAveragingRectangles D hd hI hcut Gfin
  have hP : projection D I k G f = P.1 := by
    rw [← hGfin, ← hu]
    exact Projection.projection_eq_finiteProjectionMap D hd hI hcut Gfin u
  have hmax : productMaximal (averagingRectangles D I k G) f =
      fun x => ENNReal.ofReal (M x) := by
    rw [hB, ← hu]
    exact ReyZygmund.productMaximal_eq_ofReal_finiteFamilyMaximal B u
  have hW : combinedSquareFunction D I k (projection D I k G f) =
      fun x => ENNReal.ofReal (W x) := by
    rw [hP]
    funext x
    exact combinedSquareFunction_eq_ofReal D hI hcut hd P x
  have hMleaf : ProductLeafConstant I N M :=
    ReyZygmund.productLeafConstant_finiteFamilyMaximal I N B
      (Projection.averagingRectangles_subset_productDescendants I N Gfin) u
  have hPstep := Projection.finiteProjectionMap_productStep_closure I N Gfin u hul hus
  have hWleaf : ProductLeafConstant I N W :=
    productLeafConstant_finiteComplementSquareFunction I N P hPstep.1 hPstep.2
  have hMpos (x) (hx : x ∈ productRectangle I) : 0 < M x :=
    ReyZygmund.averagingFamilyMaximal_pos (by omega) I N Gfin hdesc u hup x hx
  have hM0 (x) : 0 ≤ M x := ReyZygmund.finiteFamilyMaximal_nonneg B u x
  have hW0 (x) : 0 ≤ W x := Real.sqrt_nonneg _
  have henergy : IntegrableOn (fun x => W x ^ 2 / (M x) ^ (2 - p))
      (productRectangle I) volume := by
    apply integrableOn_productLeafConstant I N
    intro Q hQ x hx y hy
    dsimp only
    rw [hWleaf Q hQ x hx y hy, hMleaf Q hQ x hx y hy]
  have henergy0 : 0 ≤ᵐ[volume.restrict (productRectangle I)]
      (fun x => W x ^ 2 / (M x) ^ (2 - p)) := by
    filter_upwards [self_mem_ae_restrict (measurableSet_productRectangle I)] with x hx
    exact div_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos (hMpos x hx) _).le
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hnorm : ENNReal.ofReal (∫ x in productRectangle I, (f x) ^ p) =
      eLpNorm f (ENNReal.ofReal p) volume ^ p := by
    calc
      _ = ENNReal.ofReal (∫ x in productRectangle I, |f x| ^ p) := by
        congr 1
        apply setIntegral_congr_fun (measurableSet_productRectangle I)
        intro x hx
        dsimp only
        rw [abs_of_pos (hfpos x hx)]
      _ = eLpNorm f (ENNReal.ofReal p) (volume.restrict (productRectangle I)) ^ p :=
        ofReal_integral_abs_rpow_productLeafConstant_eq I N f hfl p hp0
      _ = _ := by
        rw [← eLpNorm_indicator_eq_eLpNorm_restrict
          (measurableSet_productRectangle I).nullMeasurableSet]
        change eLpNorm u.1 (ENNReal.ofReal p) volume ^ p = _
        rw [hu]
  have hraw := ReyZygmund.projected_weighted_square_conjugate I N hd Gfin hdesc
    f hfl hfpos p hp hp2
  have hbound : (∫ x in productRectangle I, W x ^ 2 / (M x) ^ (2 - p)) ≤
      (C * (p / (p - 1)) ^ (m - 1)) * ∫ x in productRectangle I, (f x) ^ p := by
    simpa only [hdim, Real.rpow_eq_pow] using hraw
  change (∫⁻ x in productRectangle I,
    combinedSquareFunction D I k (projection D I k G f) x ^ 2 /
      productMaximal (averagingRectangles D I k G) f x ^ (2 - p)) ≤ _
  rw [hW, hmax]
  calc
    _ = ∫⁻ x in productRectangle I, ENNReal.ofReal (W x ^ 2 / (M x) ^ (2 - p)) := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict (measurableSet_productRectangle I)] with x hx
      rw [← ENNReal.ofReal_pow (hW0 x) 2,
        ENNReal.ofReal_rpow_of_nonneg (hM0 x) (by linarith : 0 ≤ 2 - p),
        ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos (hMpos x hx) _)]
    _ = ENNReal.ofReal (∫ x in productRectangle I, W x ^ 2 / (M x) ^ (2 - p)) :=
      (ofReal_integral_eq_lintegral_ofReal henergy henergy0).symm
    _ ≤ ENNReal.ofReal ((C * (p / (p - 1)) ^ (m - 1)) *
        ∫ x in productRectangle I, (f x) ^ p) := ENNReal.ofReal_le_ofReal hbound
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg hC.le
        (pow_nonneg (div_nonneg hp0.le (sub_pos.mpr hp).le) _)), hnorm]

end ReyZygmund.MathlibOnly
