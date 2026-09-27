import ReyZygmund.Geometry.ProductIntegrability
import Mathlib.MeasureTheory.Integral.Prod

/-! # Integration on a fixed-coordinate slice

Coordinate insertion identifies the top rectangle with a coordinate cube times the
remaining factors, preserving Lebesgue measure. Fubini gives the integration
identity without a volume factor. Constancy on the smallest cubes gives
integrability; no sign or support assumption is needed.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Geometry

private theorem restrict_volume_root {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) :
    volume.restrict (productBox I) =
      Measure.pi (fun i => volume.restrict (I i : Set (Fin (d i) → ℝ))) := by
  exact Measure.restrict_pi_pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
    (fun i => (I i : Set (Fin (d i) → ℝ)))

variable {n : ℕ} {d : Fin (n + 1) → ℕ}

private theorem coordinateFibre_integral_core
    (I : ∀ i, Box (Fin (d i))) (H : ProductPoint d → ℝ)
    (hH : IntegrableOn H (productBox I) volume) (j : Fin (n + 1)) :
    ((∫ x in productBox I, H x) =
      ∫ t in (I j : Set (Fin (d j) → ℝ)),
        ∫ y in productBox (fun i => I (j.succAbove i)), H (j.insertNth t y)) ∧
    IntegrableOn
      (fun t => ∫ y in productBox (fun i => I (j.succAbove i)), H (j.insertNth t y))
      (I j : Set (Fin (d j) → ℝ)) volume := by
  let μ : ∀ i : Fin (n + 1), Measure (Fin (d i) → ℝ) :=
    fun i => volume.restrict (I i : Set (Fin (d i) → ℝ))
  let : ∀ i, IsFiniteMeasure (μ i) := fun i =>
    isFiniteMeasure_restrict.mpr ((I i).measure_coe_lt_top volume).ne
  let e := MeasurableEquiv.piFinSuccAbove (fun i => Fin (d i) → ℝ) j
  let G := fun z => H (e.symm z)
  have he : MeasurePreserving e (Measure.pi μ)
      ((μ j).prod (Measure.pi (fun i => μ (j.succAbove i)))) :=
    measurePreserving_piFinSuccAbove μ j
  have hH' : Integrable H (Measure.pi μ) := by
    simpa only [IntegrableOn, restrict_volume_root, μ] using hH
  have hG : Integrable G ((μ j).prod (Measure.pi (fun i => μ (j.succAbove i)))) := by
    apply (he.integrable_comp_emb e.measurableEmbedding).mp
    simpa only [G, Function.comp_def, MeasurableEquiv.symm_apply_apply] using hH'
  have hroot : Measure.pi μ = volume.restrict (productBox I) :=
    (restrict_volume_root I).symm
  have hrest : Measure.pi (fun i => μ (j.succAbove i)) =
      volume.restrict (productBox (fun i => I (j.succAbove i))) :=
    (restrict_volume_root (fun i => I (j.succAbove i))).symm
  have heq : (∫ x in productBox I, H x) =
      ∫ z, G z ∂((μ j).prod (Measure.pi (fun i => μ (j.succAbove i)))) := by
    simpa only [G, MeasurableEquiv.symm_apply_apply, hroot] using he.integral_comp' G
  have hG_apply (t : Fin (d j) → ℝ)
      (y : ProductPoint (fun i => d (j.succAbove i))) :
      G (t, y) = H (j.insertNth t y) := rfl
  constructor
  · rw [heq, integral_prod G hG]
    simp only [hG_apply, hrest, μ]
  · simpa only [hG_apply, hrest, μ, IntegrableOn] using hG.integral_prod_left

/-- Fubini's identity on the top rectangle for a function constant on the smallest cubes,
including zero depths, zero-dimensional factors and an empty remaining product. -/
theorem integral_product_coordinateFibre
    (I : ∀ i, Box (Fin (d i))) (N : Fin (n + 1) → ℕ)
    (H : ProductPoint d → ℝ) (hH : ProductLeafConstant I N H) (j : Fin (n + 1)) :
    (∫ x in productBox I, H x) =
      ∫ t in (I j : Set (Fin (d j) → ℝ)),
        ∫ y in productBox (fun i => I (j.succAbove i)), H (j.insertNth t y) :=
  (coordinateFibre_integral_core I H (integrableOn_productLeafConstant I N H hH) j).1

/-- The inner integral is integrable over the top cube in the fixed coordinate.
-/
theorem integrableOn_coordinateFibre_integral
    (I : ∀ i, Box (Fin (d i))) (N : Fin (n + 1) → ℕ)
    (H : ProductPoint d → ℝ) (hH : ProductLeafConstant I N H) (j : Fin (n + 1)) :
    IntegrableOn
      (fun t => ∫ y in productBox (fun i => I (j.succAbove i)), H (j.insertNth t y))
      (I j : Set (Fin (d j) → ℝ)) volume :=
  (coordinateFibre_integral_core I H (integrableOn_productLeafConstant I N H hH) j).2

end ReyZygmund.Geometry
