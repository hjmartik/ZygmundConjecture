import ReyZygmund.MathlibOnly.SquareFunctions
import ReyZygmund.Maximal.FiniteIdentification
import ReyZygmund.ToMathlib.Order.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # The maximal function of a finite product family

Bounded measurable inputs are integrable on every product rectangle. Their
nonnegative-integral averages therefore agree with the real absolute averages.
Taking the finite maximum gives the extended-valued maximal function.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- Nonnegative and real absolute averages give the same product maximal
function for bounded measurable inputs. -/
theorem productMaximal_eq_familyMaximal
    (G : Set (MathlibOnly.Rectangle d)) (F : boundedMeasurableFunctions d) :
    MathlibOnly.productMaximal G F.1 = familyMaximal G F.1 := by
  have hmean (R : MathlibOnly.Rectangle d) :
      (∫⁻ y in productRectangle R, ENNReal.ofReal |F.1 y| ∂volume) /
        volume (productRectangle R) =
      ENNReal.ofReal ((∫ y in productRectangle R, |F.1 y|) /
        volume.real (productRectangle R)) := by
    let : IsFiniteMeasure (volume.restrict (productRectangle R)) :=
      isFiniteMeasure_restrict.mpr (productRectangle_volume_lt_top R).ne
    obtain ⟨C, _, hC⟩ := F.2.2
    have hi : IntegrableOn F.1 (productRectangle R) volume :=
      (integrable_const C).mono' F.2.1.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun y => by
          simpa only [Real.norm_eq_abs] using hC y))
    rw [ENNReal.ofReal_div_of_pos (productRectangle_volume_pos R),
      ofReal_integral_eq_lintegral_ofReal hi.abs
        (Filter.Eventually.of_forall (fun y => abs_nonneg (F.1 y))),
      Measure.real, ENNReal.ofReal_toReal (productRectangle_volume_lt_top R).ne]
  funext x
  calc
    _ = ⨆ R : G, (productRectangle R.1).indicator
        (fun _ => (∫⁻ y in productRectangle R.1, ENNReal.ofReal |F.1 y| ∂volume) /
          volume (productRectangle R.1)) x :=
      ENNReal.iSup_mem_eq_iSup_indicator G productRectangle
        (fun R => (∫⁻ y in productRectangle R, ENNReal.ofReal |F.1 y| ∂volume) /
          volume (productRectangle R)) x
    _ = _ := by
      apply iSup_congr
      intro R
      by_cases hx : x ∈ productRectangle R.1
      · simp only [Set.indicator_of_mem hx, hmean]
      · simp only [Set.indicator_of_notMem hx, ENNReal.ofReal_zero]

/-- The extended maximal function is the nonnegative embedding of the finite
maximum of absolute averages. -/
theorem productMaximal_eq_ofReal_finiteFamilyMaximal
    (G : Finset (MathlibOnly.Rectangle d)) (F : boundedMeasurableFunctions d) :
    MathlibOnly.productMaximal (G : Set (MathlibOnly.Rectangle d)) F.1 =
      fun x => ENNReal.ofReal (finiteFamilyMaximal G F x) := by
  rw [productMaximal_eq_familyMaximal]
  funext x
  exact familyMaximal_coe_finset G F.1 x

end ReyZygmund
