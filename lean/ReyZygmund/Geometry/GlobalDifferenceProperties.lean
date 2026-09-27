import ReyZygmund.Geometry.RawDifferenceProperties
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Measurability and AE invariance of the full-grid operators

The supremum and square sum use every rectangle in the supplied
grids. These facts do not assume finite support or a finite expansion.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

theorem measurable_signedGridMaximal (D : ∀ i, DyadicGrid (d i))
    (g : ProductPoint d → ℝ) : Measurable (signedGridMaximal D g) := by
  have := (countable_gridRectangles D).to_subtype
  exact Measurable.iSup (fun Q : gridRectangles D =>
    (measurable_const.indicator (measurableSet_productBox Q.1)).ennreal_ofReal)

theorem measurable_fullGridSquare (D : ∀ i, DyadicGrid (d i))
    (g : ProductPoint d → ℝ) : Measurable (fullGridSquare D g) := by
  have := (countable_gridRectangles D).to_subtype
  unfold fullGridSquare
  have habs (Q : gridRectangles D) : Measurable
      (fun x => |rawProductDifference Q.1 g x|) := by
    simpa only [Function.comp_def, Real.norm_eq_abs] using
      continuous_norm.measurable.comp (measurable_rawProductDifference Q.1 g)
  exact (Measurable.tsum (fun Q : gridRectangles D =>
    (habs Q).ennreal_ofReal.pow_const
      (2 : ℕ))).pow_const (1 / 2 : ℝ)

theorem signedGridMaximal_congr_ae (D : ∀ i, DyadicGrid (d i))
    {g h : ProductPoint d → ℝ} (heq : g =ᵐ[volume] h) :
    signedGridMaximal D g = signedGridMaximal D h := by
  funext x
  unfold signedGridMaximal
  apply iSup_congr
  intro Q
  have hi := integral_congr_ae (ae_restrict_of_ae heq :
    g =ᵐ[volume.restrict (productBox Q.1)] h)
  rw [hi]

theorem fullGridSquare_congr_ae (D : ∀ i, DyadicGrid (d i))
    {g h : ProductPoint d → ℝ} (heq : g =ᵐ[volume] h) :
    fullGridSquare D g = fullGridSquare D h := by
  unfold fullGridSquare
  simp only [rawProductDifference_congr_ae _ heq]

end ReyZygmund.Geometry
