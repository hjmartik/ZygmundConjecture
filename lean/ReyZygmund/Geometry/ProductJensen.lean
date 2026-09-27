import ReyZygmund.Geometry.ProductSteps
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Jensen's inequality on a product rectangle

The real input and its p-th absolute power are integrable on the rectangle. The
normalized averages use product Lebesgue measure. Constancy on small cubes and
restrictions on values outside the rectangle are not needed.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- Product-box volume is positive, including empty coordinate products
and zero-dimensional factors. -/
theorem productBox_volume_pos (I : ∀ i, Box (Fin (d i))) :
    0 < volume.real (productBox I) := by
  change 0 < (Measure.pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
    (Set.pi Set.univ (fun i => (I i : Set (Fin (d i) → ℝ))))).toReal
  rw [Measure.pi_pi, ENNReal.toReal_prod]
  exact Finset.prod_pos (fun i _ => box_volume_pos (I i))

/-- Finiteness is for the product measure, not just its real-valued
conversion. The empty product has volume one. -/
theorem productBox_volume_lt_top (I : ∀ i, Box (Fin (d i))) :
    volume (productBox I) < ⊤ := by
  change Measure.pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
    (Set.pi Set.univ (fun i => (I i : Set (Fin (d i) → ℝ)))) < ⊤
  rw [Measure.pi_pi]
  exact ENNReal.prod_lt_top (fun i _ => (I i).measure_coe_lt_top volume)

/-- Normalized Jensen's inequality with coefficient one, when the input and its
absolute p-th power are integrable on the rectangle, for real p ≥ 1. -/
theorem productBox_average_abs_rpow
    (I : ∀ i, Box (Fin (d i))) (f : ProductPoint d → ℝ)
    (p : ℝ) (hp : 1 ≤ p)
    (hf : IntegrableOn f (productBox I) volume)
    (hpow : IntegrableOn (fun x => Real.rpow |f x| p) (productBox I) volume) :
    Real.rpow |(∫ x in productBox I, f x) / volume.real (productBox I)| p ≤
      (∫ x in productBox I, Real.rpow |f x| p) / volume.real (productBox I) := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hvol := productBox_volume_pos I
  have hzero : volume (productBox I) ≠ 0 := by
    intro hz
    simp [measureReal_def, hz] at hvol
  have ha : IntegrableOn (fun x => |f x|) (productBox I) volume :=
    (show Integrable f (volume.restrict (productBox I)) from hf).abs
  have hj := (convexOn_rpow hp).map_set_average_le
    (Real.continuous_rpow_const hp0).continuousOn isClosed_Ici hzero
    (productBox_volume_lt_top I).ne
    (ae_of_all _ (fun x => abs_nonneg (f x))) ha hpow
  have hj' : Real.rpow
      ((∫ x in productBox I, |f x|) / volume.real (productBox I)) p ≤
      (∫ x in productBox I, Real.rpow |f x| p) / volume.real (productBox I) := by
    simpa only [setAverage_eq, smul_eq_mul, div_eq_mul_inv, mul_comm,
      Real.rpow_eq_pow] using hj
  apply le_trans (Real.rpow_le_rpow (abs_nonneg _) ?_ hp0) hj'
  rw [abs_div, abs_of_pos hvol]
  exact div_le_div_of_nonneg_right abs_integral_le_integral_abs hvol.le

end ReyZygmund.Geometry
