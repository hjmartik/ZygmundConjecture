import ReyZygmund.MathlibOnly.SupportingStatements
import ReyZygmund.Geometry.FiniteSetting
import ReyZygmund.Weighted.OneCoordinate

/-! # Proofs of the scalar and square-function estimates

The finite partitions use the specification's cube averages and differences.
Their constant-on-bottom-cubes hypotheses give the integrability needed to
express the real integral estimates as nonnegative integrals.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.MathlibOnly

open Geometry

/-- The scalar remainder estimate, with the exact coefficient and signed increments. -/
theorem scalar_estimate : ScalarEstimate := by
  intro p a h b eta hp hp2 hb hbeta
  exact ReyZygmund.scalar_estimate p a h b eta hp hp2 hb hbeta

/-- The one-coordinate weighted estimate on a grid with the prescribed smallest scale. -/
theorem weighted_square_function_estimate : WeightedSquareFunctionEstimate := by
  intro d hd D I k htop u v hu hv hvpos p hp hp2
  obtain ⟨l, hI, hcut⟩ := htop
  let N := (l + k).toNat
  have hul : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, u x = u y :=
    (constantOnBottomCubes_iff D hI hcut u).mp hu
  have hvl : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, v x = v y :=
    (constantOnBottomCubes_iff D hI hcut v).mp hv
  have hvi := integrableOn_of_leafConstant I N v hvl
  have hmean (Q : Box (Fin d)) (hQ : Q ∈ interior I N) : 0 < cubeMean Q v := by
    have hQI := le_of_mem_descendants (interior_subset_descendants I N hQ)
    exact cubeMean_pos Q v (hvi.mono_set hQI) (fun x hx => hvpos x (hQI hx))
  have hleft (Q : Box (Fin d)) (hQ : Q ∈ interior I N) :
      ∀ x, 0 ≤ (cubeDifference Q u x) ^ 2 / (cubeMean Q v) ^ (2 - p) :=
    fun x => div_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos (hmean Q hQ) _).le
  have hright : IntegrableOn (fun x => (u x) ^ 2 / (v x) ^ (2 - p))
      (I : Set (Fin d → ℝ)) volume := by
    apply integrableOn_of_leafConstant I N
    intro Q hQ x hx y hy
    rw [hul Q hQ x hx y hy, hvl Q hQ x hx y hy]
  have hright_nonneg : 0 ≤ᵐ[volume.restrict (I : Set (Fin d → ℝ))]
      (fun x => (u x) ^ 2 / (v x) ^ (2 - p)) :=
    (ae_restrict_iff' I.measurableSet_coe).mpr
      (Filter.Eventually.of_forall fun x hx =>
        div_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos (hvpos x hx) _).le)
  have hC : 0 ≤ (2 : ℝ) ^ ((d : ℝ) * (2 - p)) * ((3 - p) / (p - 1)) :=
    mul_nonneg (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
      (div_nonneg (by linarith) (by linarith))
  rw [interiorCubes_eq_interior D hd hI hcut,
    Finset.tsum_subtype' (interior I (l + k).toNat)
      (fun Q => ∫⁻ x in (Q : Set (Fin d → ℝ)),
        ENNReal.ofReal ((cubeDifference Q u x) ^ 2 / (cubeMean Q v) ^ (2 - p)))]
  change (∑ Q ∈ interior I N, ∫⁻ x in (Q : Set (Fin d → ℝ)),
    ENNReal.ofReal ((cubeDifference Q u x) ^ 2 / (cubeMean Q v) ^ (2 - p))) ≤ _
  calc
    _ = ∑ Q ∈ interior I N, ENNReal.ofReal
        (∫ x in (Q : Set (Fin d → ℝ)),
          (cubeDifference Q u x) ^ 2 / (cubeMean Q v) ^ (2 - p)) := by
      apply Finset.sum_congr rfl
      intro Q hQ
      exact (ofReal_integral_eq_lintegral_ofReal
        (integrableOn_comp_cubeDifference Q u (fun a => a ^ 2 / (cubeMean Q v) ^ (2 - p)))
        (Filter.Eventually.of_forall (hleft Q hQ))).symm
    _ = ENNReal.ofReal (∑ Q ∈ interior I N,
        ∫ x in (Q : Set (Fin d → ℝ)),
          (cubeDifference Q u x) ^ 2 / (cubeMean Q v) ^ (2 - p)) :=
      (ENNReal.ofReal_sum_of_nonneg (fun Q hQ => integral_nonneg (hleft Q hQ))).symm
    _ ≤ ENNReal.ofReal (((2 : ℝ) ^ ((d : ℝ) * (2 - p)) * ((3 - p) / (p - 1))) *
        ∫ x in (I : Set (Fin d → ℝ)), (u x) ^ 2 / (v x) ^ (2 - p)) :=
      ENNReal.ofReal_le_ofReal (ReyZygmund.weighted_square d hd I N u v p hp hp2
        hul hvl hvpos)
    _ = _ := by
      rw [ENNReal.ofReal_mul hC, ofReal_integral_eq_lintegral_ofReal hright hright_nonneg]

end ReyZygmund.MathlibOnly
