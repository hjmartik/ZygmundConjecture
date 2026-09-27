import ReyZygmund.Geometry.FlatRectangles
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # Finite overlap and its shadow

The overlap is the sum of the indicators of the Euclidean rectangles.
No geometry, sparseness or estimate is built into either definition.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Overlap

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- The union of a finite family of Euclidean rectangles. -/
def finiteShadow (G : Finset (∀ i, Box (Fin (d i)))) : Set (Fin (∑ i, d i) → ℝ) :=
  ⋃ Q ∈ G, (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ))

/-- The number of rectangles of the finite family containing a point. -/
noncomputable def finiteOverlap (G : Finset (∀ i, Box (Fin (d i))))
    (x : Fin (∑ i, d i) → ℝ) : ℝ :=
  ∑ Q ∈ G, (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)).indicator (fun _ => 1) x

theorem flatProductBox_subset_finiteShadow
    (G : Finset (∀ i, Box (Fin (d i)))) (Q : ∀ i, Box (Fin (d i))) (hQ : Q ∈ G) :
    (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ⊆ finiteShadow G :=
  Set.subset_iUnion_of_subset Q (Set.subset_iUnion_of_subset hQ Set.Subset.rfl)

theorem measurableSet_finiteShadow (G : Finset (∀ i, Box (Fin (d i)))) :
    MeasurableSet (finiteShadow G) :=
  Finset.measurableSet_biUnion G (fun Q _ => (flatProductBox Q).measurableSet_coe)

theorem volume_finiteShadow_lt_top (G : Finset (∀ i, Box (Fin (d i)))) :
    volume (finiteShadow G) < ∞ := by
  apply measure_biUnion_lt_top G.finite_toSet
  intro Q _
  exact (flatProductBox Q).isBounded.measure_lt_top

theorem measurable_finiteOverlap (G : Finset (∀ i, Box (Fin (d i)))) :
    Measurable (finiteOverlap G) :=
  Finset.measurable_sum G (fun Q _ =>
    measurable_const.indicator (flatProductBox Q).measurableSet_coe)

theorem finiteOverlap_nonneg (G : Finset (∀ i, Box (Fin (d i))))
    (x : Fin (∑ i, d i) → ℝ) : 0 ≤ finiteOverlap G x :=
  Finset.sum_nonneg (fun _Q _ => Set.indicator_nonneg (fun _ _ => zero_le_one) x)

theorem finiteOverlap_le_card (G : Finset (∀ i, Box (Fin (d i))))
    (x : Fin (∑ i, d i) → ℝ) : finiteOverlap G x ≤ G.card := by
  calc
    _ ≤ ∑ _Q ∈ G, (1 : ℝ) := Finset.sum_le_sum (fun Q _ => by
      by_cases hx : x ∈ (flatProductBox Q : Set _)
      · simp only [Set.indicator_of_mem hx, le_refl]
      · simp only [Set.indicator_of_notMem hx, zero_le_one])
    _ = _ := by simp

theorem finiteOverlap_eq_zero_of_not_mem
    (G : Finset (∀ i, Box (Fin (d i)))) (x : Fin (∑ i, d i) → ℝ)
    (hx : x ∉ finiteShadow G) : finiteOverlap G x = 0 := by
  apply Finset.sum_eq_zero
  intro Q hQ
  exact Set.indicator_of_notMem
    (fun h => hx (flatProductBox_subset_finiteShadow G Q hQ h)) _

theorem memLp_finiteOverlap (G : Finset (∀ i, Box (Fin (d i)))) (p : ℝ≥0∞) :
    MemLp (finiteOverlap G) p volume := by
  apply memLp_finsetSum
  intro Q _
  apply memLp_indicator_const p (flatProductBox Q).measurableSet_coe (1 : ℝ)
  right
  exact (flatProductBox Q).isBounded.measure_lt_top.ne

theorem integrable_rpow_finiteOverlap
    (G : Finset (∀ i, Box (Fin (d i)))) (q : ℝ) (hq : 0 < q) :
    Integrable (fun x => Real.rpow (finiteOverlap G x) q) volume := by
  have h := (memLp_finiteOverlap G (ENNReal.ofReal q)).integrable_norm_rpow
    (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top
  simpa only [Real.norm_eq_abs, abs_of_nonneg (finiteOverlap_nonneg G _),
    ENNReal.toReal_ofReal hq.le, Real.rpow_eq_pow] using h

end ReyZygmund.Overlap
