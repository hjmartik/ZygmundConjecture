import ReyZygmund.MathlibOnly.SupportingStatements
import ReyZygmund.Geometry.ProductFiniteSetting
import ReyZygmund.Geometry.PartialOperatorMaps
import ReyZygmund.Geometry.ProductLp
import ReyZygmund.Weighted.Product

/-! # The independent product weighted square-function estimate

Tuples of selected cubes index the finite product regions. The coordinate
averages and differences agree with the operators used in the weighted
iteration. Integrability identifies the real and nonnegative energy integrals.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.MathlibOnly

open Geometry

/-- The product weighted estimate with a common smallest scale in all coordinates. -/
theorem product_weighted_square_function_estimate : ProductWeightedSquareFunctionEstimate := by
  intro m _hm d hd D I k htop f hs hfpos hf A _hA p hp hp2
  choose l hI hcut using htop
  let N := fun i => (l i + k).toNat
  have hfl : ProductLeafConstant I N f :=
    (constantOnBottomRectangles_iff D hI hcut f).mp hf
  let F := finiteInput I N f hfl
  have hF : F.1 = f := finiteInput_eq I N f hfl hs
  have hDifference (Q : Rectangle d) :
      partialDifference A (fun i => Q i) f = (productDifferenceMap A Q F).1 := by
    simpa only [hF] using partialDifference_eq_productDifferenceMap A Q F
  have hAverage (Q : Rectangle d) :
      partialAverage A (fun i => Q i) f = (productAverageMap A Q F).1 := by
    simpa only [hF] using partialAverage_eq_productAverageMap A Q F
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hC : 0 ≤ (2 : ℝ) ^ ((2 - p) * ∑ i ∈ A, (d i : ℝ)) *
      ((3 - p) / (p - 1)) ^ A.card :=
    mul_nonneg (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
      (pow_nonneg (div_nonneg (by linarith) (by linarith)) _)
  have henergy_nonneg (Q : Rectangle d) (hQ : Q ∈ Geometry.partialInterior I N A) :
      0 ≤ᵐ[volume.restrict (productRectangle Q)]
        (fun x => ((productDifferenceMap A Q F).1 x) ^ 2 /
          ((productAverageMap A Q F).1 x) ^ (2 - p)) := by
    filter_upwards [self_mem_ae_restrict (measurableSet_productRectangle Q)] with x hx
    exact div_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos
      (ReyZygmund.product_energy_average_pos I N f hfl hfpos A Q hQ x hx) _).le
  have henergy_integral_nonneg (Q : Rectangle d)
      (hQ : Q ∈ Geometry.partialInterior I N A) :
      0 ≤ ∫ x in productRectangle I, ((productDifferenceMap A Q F).1 x) ^ 2 /
        ((productAverageMap A Q F).1 x) ^ (2 - p) := by
    have h := integral_nonneg_of_ae (henergy_nonneg Q hQ)
    have hcyl := ReyZygmund.product_energy_integral_cylinder I N f hfl A Q hQ p
    simp only [Real.rpow_eq_pow] at hcyl
    rwa [← hcyl] at h
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
        change eLpNorm F.1 (ENNReal.ofReal p) volume ^ p = _
        rw [hF]
  calc
    _ = ∑ Q ∈ Geometry.partialInterior I N A, ENNReal.ofReal
        (∫ x in productRectangle I, ((productDifferenceMap A Q F).1 x) ^ 2 /
          ((productAverageMap A Q F).1 x) ^ (2 - p)) := by
      rw [tsum_partialInterior_eq D hI hcut A (fun i _ => hd i)
        (fun K => ∫⁻ x in partialRectangleRegion I A K,
          ENNReal.ofReal ((partialDifference A K f x) ^ 2 /
            (partialAverage A K f x) ^ (2 - p)))]
      apply Finset.sum_congr rfl
      intro Q hQ
      rw [partialRectangle_eq_productRectangle, completePartialRectangle_restrict I N A hQ,
        hDifference Q, hAverage Q]
      have hcyl := ReyZygmund.product_energy_integral_cylinder I N f hfl A Q hQ p
      simp only [Real.rpow_eq_pow] at hcyl
      rw [hcyl]
      exact (ofReal_integral_eq_lintegral_ofReal
        (ReyZygmund.product_energy_integrable I N f hfl A Q hQ p).2
        (henergy_nonneg Q hQ)).symm
    _ = ENNReal.ofReal (∑ Q ∈ Geometry.partialInterior I N A,
        ∫ x in productRectangle I, ((productDifferenceMap A Q F).1 x) ^ 2 /
          ((productAverageMap A Q F).1 x) ^ (2 - p)) :=
      (ENNReal.ofReal_sum_of_nonneg henergy_integral_nonneg).symm
    _ ≤ ENNReal.ofReal (((2 : ℝ) ^ ((2 - p) * ∑ i ∈ A, (d i : ℝ)) *
        ((3 - p) / (p - 1)) ^ A.card) *
          ∫ x in productRectangle I, (f x) ^ p) :=
      ENNReal.ofReal_le_ofReal
        (ReyZygmund.product_weighted_square I N f hfl hfpos p hp hp2 A (fun i _ => hd i))
    _ = _ := by rw [ENNReal.ofReal_mul hC, hnorm]

end ReyZygmund.MathlibOnly
