import ReyZygmund.MathlibOnly.SupportingStatements
import ReyZygmund.Geometry.RoundedSlicesIco
import ReyZygmund.Geometry.ShiftedGrid
import ReyZygmund.Selection.SliceSparsity

/-! # Weak incomparability and half-sparsity of slices

The public slice statements use the shared projection and slice definitions.
Half-sparsity follows by ordering the last-coordinate cubes, subtracting earlier
projections and cancelling the positive measure of the last cube.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.MathlibOnly

/-- Slices of incomparable rounded families are weakly incomparable, have
unique original rectangles, and preserve overlap at every point. -/
theorem weakly_incomparable_slices : WeaklyIncomparableSlices := by
  intro n hn d _hd phi hphi tau G hG hinc t
  let D := fun i => Geometry.shiftedDyadicGrid (d i) (tau i)
  have hrounded : G ⊆ Geometry.roundedGridRectangles D phi := by
    rintro R hR
    obtain ⟨k, hk, hRk⟩ := hG hR
    refine ⟨k, hk, fun i => ?_⟩
    simpa only [D, CubeGrid.cubesAtGeneration_neg, Geometry.shiftedDyadicGrid_cubes, neg_neg]
      using hRk i
  have hgrid : G ⊆ gridRectangles D :=
    hrounded.trans (Geometry.roundedGridRectangles_subset D phi)
  exact ⟨Geometry.sliceFamilyIco_weaklyIncomparable (by omega) D phi hphi G hrounded hinc t,
    fun _ hP => Geometry.sliceFamilyIco_existsUnique D G hgrid hinc t hP,
    fun x => Geometry.overlapIco_appendLastPoint D G hgrid hinc x t⟩

/-- Every fixed slice of a finite family with the half-overlap bound is
half-sparse, with Lebesgue-measurable disjoint subsets. -/
theorem half_sparse_slices : HalfSparseSlices := by
  intro n _hn d _hd D G hfinite hG hoverlap t
  have hoverlap' : ∀ R ∈ hfinite.toFinset,
      volume.real ((Geometry.flatProductBox R : Set (Point d)) ∩
        Overlap.finiteShadow (hfinite.toFinset.erase R)) ≤
        (1 / 2 : ℝ) * volume.real (Geometry.flatProductBox R : Set (Point d)) := by
    intro R hR
    have h := hoverlap R (hfinite.mem_toFinset.mp hR)
    have herase : G \ {R} = (↑(hfinite.toFinset.erase R) : Set (Rectangle d)) := by
      simp
    rw [herase, ← Overlap.finiteShadow_eq_shadow,
      Geometry.rectangle_eq_flatProductBox] at h
    have htop : (1 / 2 : ℝ≥0∞) *
        volume (Geometry.flatProductBox R : Set (Point d)) ≠ ∞ :=
      ENNReal.mul_ne_top (by norm_num) (Geometry.flatProductBox R).isBounded.measure_lt_top.ne
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_one, ENNReal.toReal_ofNat] using ENNReal.toReal_mono htop h
  obtain ⟨E, hE, hdisj⟩ := Selection.finite_slice_half_sparse D hfinite.toFinset
    (by simpa using hG) hoverlap' t
  refine ⟨E, ?_, ?_⟩
  · intro P hP
    have h := hE P (by simpa using hP)
    exact ⟨h.1.nullMeasurableSet,
      by simpa only [Geometry.rectangle_eq_flatProductBox] using h.2.1,
      by simpa only [Geometry.rectangle_eq_flatProductBox] using h.2.2⟩
  · simpa using hdisj

end ReyZygmund.MathlibOnly
