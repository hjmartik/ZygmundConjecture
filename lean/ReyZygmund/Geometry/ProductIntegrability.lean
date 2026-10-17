import ReyZygmund.Geometry.ProductSteps

/-! # Integrability on the top rectangle

Constancy on the smallest product cubes gives a bounded measurable restriction to
the top rectangle, and hence integrability of the nonlinear finite energies used
later.
-/

open BoxIntegral MeasureTheory
open scoped ENNReal

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

theorem integrableOn_productLeafConstant
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f) :
    IntegrableOn f (productRectangle I) volume := by
  have hvol : volume (productRectangle I) < ∞ := productRectangle_volume_lt_top I
  let : IsFiniteMeasure (volume.restrict (productRectangle I)) :=
    isFiniteMeasure_restrict.mpr hvol.ne
  obtain ⟨C, _, hC⟩ := bounded_product_localization I N f hf
  have hl : IntegrableOn ((productRectangle I).indicator f) (productRectangle I) volume :=
    (integrable_const C).mono'
      (measurable_product_localization I N f hf).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs] using hC x))
  exact hl.congr_fun (fun x hx => Set.indicator_of_mem hx f)
    (measurableSet_productRectangle I)

end ReyZygmund.Geometry
