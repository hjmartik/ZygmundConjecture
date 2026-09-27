import ReyZygmund.Geometry.GlobalDifferences
import ReyZygmund.Geometry.ProductJensen

/-! # Integrability of finite difference expansions

The finite expansion of rectangle integrals is a bounded Borel function and is
Lebesgue integrable. An input equal almost everywhere to such an expansion is
therefore integrable, as required in the full-grid square theorem.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

theorem measurable_rawProductDifference (Q : ∀ i, Box (Fin (d i)))
    (g : ProductPoint d → ℝ) : Measurable (rawProductDifference Q g) := by
  apply Finset.measurable_sum
  intro A _
  apply Measurable.const_mul
  exact Finset.measurable_sum _ (fun R _ =>
    measurable_const.indicator (measurableSet_productBox R))

theorem bounded_rawProductDifference (Q : ∀ i, Box (Fin (d i)))
    (g : ProductPoint d → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |rawProductDifference Q g x| ≤ C := by
  refine ⟨∑ A ∈ (Finset.univ : Finset (Fin m)).powerset,
    ∑ R ∈ differenceRectangles A Q,
      |(∫ y in productBox R, g y) / volume.real (productBox R)|,
    Finset.sum_nonneg (fun A _ => Finset.sum_nonneg (fun R _ => abs_nonneg _)), ?_⟩
  intro x
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro A _
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro R _
  by_cases hx : x ∈ productBox R
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, abs_zero]
    exact abs_nonneg _

theorem integrable_rawProductDifference (Q : ∀ i, Box (Fin (d i)))
    (g : ProductPoint d → ℝ) : Integrable (rawProductDifference Q g) volume := by
  apply integrable_finsetSum
  intro A _
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro R _
  exact (integrableOn_const (productBox_volume_lt_top R).ne).integrable_indicator
    (measurableSet_productBox R)

/-- The finite coefficient expansion as a bounded measurable function. -/
noncomputable def rawDifferenceInput (Q : ∀ i, Box (Fin (d i)))
    (g : ProductPoint d → ℝ) : boundedMeasurableFunctions d :=
  ⟨rawProductDifference Q g, measurable_rawProductDifference Q g,
    bounded_rawProductDifference Q g⟩

theorem rawProductDifference_congr_ae (Q : ∀ i, Box (Fin (d i)))
    {g h : ProductPoint d → ℝ} (heq : g =ᵐ[volume] h) :
    rawProductDifference Q g = rawProductDifference Q h := by
  funext x
  apply Finset.sum_congr rfl
  intro A _
  congr 1
  apply Finset.sum_congr rfl
  intro R _
  have hi := integral_congr_ae (ae_restrict_of_ae heq :
    g =ᵐ[volume.restrict (productBox R)] h)
  rw [hi]

theorem finite_raw_expansion_integrable
    (H : Finset (∀ i, Box (Fin (d i)))) (g : ProductPoint d → ℝ)
    (heq : g =ᵐ[volume] fun x => ∑ Q ∈ H, rawProductDifference Q g x) :
    Integrable g volume :=
  (integrable_finsetSum H (fun Q _ => integrable_rawProductDifference Q g)).congr heq.symm

/-- The finite bounded representative retains the original input almost
everywhere and retains every full difference pointwise. -/
theorem finite_raw_expansion_representative
    (H : Finset (∀ i, Box (Fin (d i)))) (g : ProductPoint d → ℝ)
    (heq : g =ᵐ[volume] fun x => ∑ Q ∈ H, rawProductDifference Q g x) :
    ∃ F : boundedMeasurableFunctions d,
      (g =ᵐ[volume] F.1) ∧ Integrable F.1 volume ∧
      (∀ Q, rawProductDifference Q g = rawProductDifference Q F.1) ∧
      (F.1 = fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x) := by
  let F : boundedMeasurableFunctions d := ∑ Q ∈ H, rawDifferenceInput Q g
  have hF : F.1 = fun x => ∑ Q ∈ H, rawProductDifference Q g x := by
    funext x
    simp [F, rawDifferenceInput, Finset.sum_apply]
  have hgf : g =ᵐ[volume] F.1 := heq.trans (Filter.Eventually.of_forall (congrFun hF.symm))
  refine ⟨F, hgf, (finite_raw_expansion_integrable H g heq).congr hgf, ?_, ?_⟩
  · intro Q
    exact rawProductDifference_congr_ae Q hgf
  · calc
      F.1 = fun x => ∑ Q ∈ H, rawProductDifference Q g x := hF
      _ = fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x := by
        funext x
        apply Finset.sum_congr rfl
        intro Q _
        exact congrFun (rawProductDifference_congr_ae Q hgf) x

end ReyZygmund.Geometry
