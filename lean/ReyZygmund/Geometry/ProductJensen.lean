import ReyZygmund.Geometry.ProductSteps
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Jensen's inequality on a product rectangle

The real input and its p-th absolute power are integrable on the rectangle.
The normalized averages use product Lebesgue measure.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- Normalized Jensen's inequality with coefficient one, when the input and its
absolute p-th power are integrable on the rectangle, for real p ≥ 1. -/
theorem productRectangle_average_abs_rpow
    (I : ∀ i, Box (Fin (d i))) (f : ProductPoint d → ℝ)
    (p : ℝ) (hp : 1 ≤ p)
    (hf : IntegrableOn f (productRectangle I) volume)
    (hpow : IntegrableOn (fun x => Real.rpow |f x| p) (productRectangle I) volume) :
    Real.rpow |(∫ x in productRectangle I, f x) / volume.real (productRectangle I)| p ≤
      (∫ x in productRectangle I, Real.rpow |f x| p) / volume.real (productRectangle I) := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hvol := productRectangle_volume_pos I
  have hzero : volume (productRectangle I) ≠ 0 := by
    intro hz
    simp [measureReal_def, hz] at hvol
  have ha : IntegrableOn (fun x => |f x|) (productRectangle I) volume :=
    (show Integrable f (volume.restrict (productRectangle I)) from hf).abs
  have hj := (convexOn_rpow hp).map_set_average_le
    (Real.continuous_rpow_const hp0).continuousOn isClosed_Ici hzero
    (productRectangle_volume_lt_top I).ne
    (ae_of_all _ (fun x => abs_nonneg (f x))) ha hpow
  have hj' : Real.rpow
      ((∫ x in productRectangle I, |f x|) / volume.real (productRectangle I)) p ≤
      (∫ x in productRectangle I, Real.rpow |f x| p) / volume.real (productRectangle I) := by
    simpa only [setAverage_eq, smul_eq_mul, div_eq_mul_inv, mul_comm,
      Real.rpow_eq_pow] using hj
  apply le_trans (Real.rpow_le_rpow (abs_nonneg _) ?_ hp0) hj'
  rw [abs_div, abs_of_pos hvol]
  exact div_le_div_of_nonneg_right abs_integral_le_integral_abs hvol.le

end ReyZygmund.Geometry
