import ReyZygmund.MathlibOnly.SupportingStatements
import ReyZygmund.MathlibOnly.Representation
import ReyZygmund.MathlibOnly.Proof.OperatorBridge
import ReyZygmund.Geometry.RawDifferenceBridge
import ReyZygmund.Maximal.GlobalSquare

/-! # The independent maximal–square-function estimate

A finite martingale expansion is bounded and measurable. Its coordinate
differences agree with the rectangle-integral formula used in the full-grid
estimate, which then gives the required norm bound.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.MathlibOnly

open Geometry

namespace Proof

/-- The specification's signed maximal function agrees with the library's full-grid version. -/
theorem signedMaximal_eq_signedGridMaximal {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, CubeGrid (d i)) (g : ProductPoint d → ℝ) :
    signedMaximal D g = Geometry.signedGridMaximal D g := by
  funext x
  rw [signedMaximal, ENNReal.iSup_mem_eq_iSup_indicator]
  unfold Geometry.signedGridMaximal
  apply iSup_congr
  intro R
  by_cases hx : x ∈ productRectangle R.1
  · simp only [Set.indicator_of_mem hx]
  · simp only [Set.indicator_of_notMem hx, ENNReal.ofReal_zero]

/-- The square series agrees term by term on bounded measurable functions. -/
theorem squareFunction_eq_fullGridSquare {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, CubeGrid (d i)) (F : boundedMeasurableFunctions d) :
    squareFunction D F.1 = Geometry.fullGridSquare D F.1 := by
  funext x
  unfold squareFunction Geometry.fullGridSquare
  simp only [fullDifference_eq_rawProductDifference _ F]

end Proof

/-- The product maximal–square estimate, including one factor and `p = 1`. -/
theorem maximal_square_function_estimate : MaximalSquareFunctionEstimate := by
  intro m _hm d hd D H hH g hex p hp hp3
  have hg : Measurable g := hex ▸ measurable_sum_fullDifference H g
  have hbounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |g x| ≤ C :=
    hex ▸ bounded_sum_fullDifference H g
  let F : boundedMeasurableFunctions d := ⟨g, hg, hbounded⟩
  have hraw : F.1 = fun x => ∑ R ∈ H, rawProductDifference R F.1 x := by
    calc
      F.1 = (fun x => ∑ R ∈ H, fullDifference R F.1 x) := hex
      _ = _ := by simp only [fullDifference_eq_rawProductDifference _ F]
  obtain ⟨_, _, _, hMfinite, hSfinite, _, _, hbound⟩ :=
    ReyZygmund.full_grid_square_estimate D hd H hH F.1
      (Filter.Eventually.of_forall (congrFun hraw)) p hp hp3
  change eLpNorm (signedMaximal D F.1) (ENNReal.ofReal p) volume ≤
    ENNReal.ofReal ((2 : ℝ) ^ (6 * (∑ i, d i) + 10)) *
      eLpNorm (squareFunction D F.1) (ENNReal.ofReal p) volume
  rw [Proof.signedMaximal_eq_signedGridMaximal,
    Proof.squareFunction_eq_fullGridSquare,
    eLpNorm_eq_toReal _ hMfinite, eLpNorm_eq_toReal _ hSfinite]
  exact hbound

end ReyZygmund.MathlibOnly
