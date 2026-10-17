import ReyZygmund.MathlibOnly.Definitions
import ReyZygmund.MathlibOnly.Proof.MaximalFormulas
import ReyZygmund.Maximal.Euclidean
import ReyZygmund.Geometry.ShiftedGrid
import ReyZygmund.Geometry.RoundedScales
import ReyZygmund.Geometry.ProductJensen
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Real-integral maximal functions and explicit shifted grids

Local integrability identifies the nonnegative and real averages. The explicit
shifted cubes agree with the corresponding grid constructor, so its rounded
family is the specialization to those grids.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.MathlibOnly.Proof

noncomputable section

/-- Integrability on the selected rectangles identifies the nonnegative
averages with real absolute means before taking their supremum. -/
theorem maximal_eq_euclidean_of_integrableOn {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i)))) (f : (Fin (∑ i, d i) → ℝ) → ℝ)
    (hf : ∀ R ∈ G, IntegrableOn f
      (Geometry.flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) volume) :
    maximal G f = euclideanFamilyMaximal G f := by
  rw [maximal_eq_iSup_indicator]
  funext x
  unfold euclideanFamilyMaximal
  congr 1
  funext R
  rw [Geometry.rectangle_eq_flatProductBox]
  have hv : volume (Geometry.flatProductBox R.1 : Set (Fin (∑ i, d i) → ℝ)) < ∞ := by
    rw [Geometry.volume_flatProductBox]
    exact Geometry.productRectangle_volume_lt_top R.1
  have hvpos : 0 < volume.real
      (Geometry.flatProductBox R.1 : Set (Fin (∑ i, d i) → ℝ)) := by
    rw [Measure.real, Geometry.volume_flatProductBox]
    exact Geometry.productRectangle_volume_pos R.1
  by_cases hx : x ∈ (Geometry.flatProductBox R.1 : Set (Fin (∑ i, d i) → ℝ))
  · simp only [Set.indicator_of_mem hx]
    rw [ENNReal.ofReal_div_of_pos hvpos,
      ofReal_integral_eq_lintegral_ofReal (hf R.1 R.2).abs
        (Filter.Eventually.of_forall (fun y => abs_nonneg (f y))),
      Measure.real, ENNReal.ofReal_toReal hv.ne]
  · simp only [Set.indicator_of_notMem hx, ENNReal.ofReal_zero]

/-- For locally integrable inputs, the maximal function agrees with its
real-integral formulation. -/
theorem maximal_eq_euclidean_of_locallyIntegrable {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i)))) (f : (Fin (∑ i, d i) → ℝ) → ℝ)
    (hf : LocallyIntegrable f volume) :
    maximal G f = euclideanFamilyMaximal G f := by
  apply maximal_eq_euclidean_of_integrableOn G f
  intro R _hR
  exact (hf.integrableOn_isCompact (Geometry.flatProductBox R).isCompact_Icc).mono_set
    Box.coe_subset_Icc

/-- An `L^p` function with `p > 1` is integrable on every bounded rectangle. -/
theorem maximal_eq_euclidean_of_memLp {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    maximal G f = euclideanFamilyMaximal G f := by
  apply maximal_eq_euclidean_of_integrableOn G f
  intro R _hR
  have hv : volume (Geometry.flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) < ∞ := by
    rw [Geometry.volume_flatProductBox]
    exact Geometry.productRectangle_volume_lt_top R
  let : IsFiniteMeasure (volume.restrict
      (Geometry.flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) :=
    isFiniteMeasure_restrict.mpr hv.ne
  exact MemLp.integrable (by simpa using ENNReal.ofReal_le_ofReal hp.le) (hf.restrict _)

/-- The explicit shifted cubes at side exponent `k` are the alternating
grid cubes at generation `-k`. -/
theorem shiftedCubes_eq {d : ℕ} (tau : Fin d → Fin 3) (k : ℤ) :
    shiftedCubes tau k = (Geometry.shiftedDyadicGrid d tau).cubesAtGeneration (-k) := by
  simpa only [CubeGrid.cubesAtGeneration_neg] using
    (Geometry.shiftedDyadicGrid_cubes d tau k).symm

theorem roundedRectangles_eq {n : ℕ} {d : Fin (n + 1) → ℕ}
    (tau : ∀ i, Fin (d i) → Fin 3)
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) :
    roundedRectangles tau phi = Geometry.roundedGridRectangles
      (fun i => Geometry.shiftedDyadicGrid (d i) (tau i)) phi := by
  simp only [roundedRectangles, Geometry.roundedGridRectangles,
    shiftedCubes_eq]

end
end ReyZygmund.MathlibOnly.Proof
