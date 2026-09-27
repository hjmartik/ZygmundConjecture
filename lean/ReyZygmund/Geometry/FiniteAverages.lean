import Mathlib.Analysis.BoxIntegral.Partition.Measure
import Mathlib.Analysis.BoxIntegral.Partition.SubboxInduction
import Mathlib.MeasureTheory.Integral.Bochner.Set
import ReyZygmund.Geometry.FiniteCubes

/-! # Lebesgue averages on finite dyadic cubes

The averaging operator integrates over a half-open cube. We prove its partition
and telescoping identities from this definition.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

variable {d : ℕ}

/-- Local average, extended by zero outside the box. -/
noncomputable def boxAverage (Q : Box (Fin d)) (g : (Fin d → ℝ) → ℝ) :
    (Fin d → ℝ) → ℝ :=
  (Q : Set (Fin d → ℝ)).indicator
    (fun _ => (∫ x in (Q : Set (Fin d → ℝ)), g x) / volume.real (Q : Set (Fin d → ℝ)))

/-- One-coordinate martingale difference: child averages minus parent average. -/
noncomputable def boxDifference (Q : Box (Fin d)) (g : (Fin d → ℝ) → ℝ) :
    (Fin d → ℝ) → ℝ :=
  (∑ R ∈ (Prepartition.splitCenter Q).boxes, boxAverage R g) - boxAverage Q g

theorem box_volume_pos (Q : Box (Fin d)) :
    0 < volume.real (Q : Set (Fin d → ℝ)) := by
  rw [measureReal_def, Box.volume_apply']
  exact Finset.prod_pos (fun i _ => sub_pos.mpr (Q.lower_lt_upper i))

/-- Concrete realization at every cutoff: cubes, finite positive Lebesgue
volume, a pointwise partition, dyadic widths and all `2^d` children. -/
theorem finite_cube_realization (d : ℕ) (lower : Fin d → ℝ) (a : ℤ) (N : ℕ) :
    (level (rootBox lower a) N).IsPartition ∧
    ∀ Q ∈ leaves (rootBox lower a) N,
      0 < volume.real (Q : Set (Fin d → ℝ)) ∧
      volume (Q : Set (Fin d → ℝ)) < ⊤ ∧
      (∀ i : Fin d, Q.upper i - Q.lower i = (2 : ℝ) ^ (a - (N : ℤ))) ∧
      (Prepartition.splitCenter Q).boxes.card = 2 ^ d := by
  refine ⟨level_isPartition _ _, ?_⟩
  intro Q hQ
  refine ⟨box_volume_pos Q, Q.measure_coe_lt_top volume, ?_, ?_⟩
  · exact fun i => rootBox_level_width hQ i
  · simpa using splitCenter_card Q

theorem boxAverage_of_constant (Q : Box (Fin d)) (g : (Fin d → ℝ) → ℝ)
    (hg : ∀ x ∈ Q, ∀ y ∈ Q, g x = g y) :
    boxAverage Q g = (Q : Set (Fin d → ℝ)).indicator g := by
  funext x
  by_cases hx : x ∈ Q
  · have hi : (∫ y in (Q : Set (Fin d → ℝ)), g y) =
        volume.real (Q : Set (Fin d → ℝ)) * g x := by
      calc
        _ = ∫ _ in (Q : Set (Fin d → ℝ)), g x :=
          setIntegral_congr_fun Q.measurableSet_coe (fun y hy => hg y hy x hx)
        _ = _ := by rw [setIntegral_const, smul_eq_mul]
    simp only [boxAverage, Set.indicator_of_mem (show x ∈ (Q : Set (Fin d → ℝ)) from hx), hi]
    exact mul_div_cancel_left₀ (g x) (ne_of_gt (box_volume_pos Q))
  · simp [boxAverage, hx]

/-- The sum of partition indicators equals the indicator of the top cube, pointwise. -/
theorem sum_box_indicators {I : Box (Fin d)} (π : Prepartition I)
    (hπ : π.IsPartition) (g : (Fin d → ℝ) → ℝ) :
    (∑ Q ∈ π.boxes, (Q : Set (Fin d → ℝ)).indicator g) =
      (I : Set (Fin d → ℝ)).indicator g := by
  classical
  funext x
  simp only [Finset.sum_apply]
  by_cases hx : x ∈ I
  · obtain ⟨Q, hQ, hxQ⟩ := hπ x hx
    rw [Finset.sum_eq_single Q]
    · simp [hx, hxQ]
    · intro R hR hRQ
      have hxR : x ∉ R := fun h => hRQ (π.eq_of_mem_of_mem hR hQ h hxQ)
      exact Set.indicator_of_notMem hxR g
    · simp [hQ]
  · have hout : ∀ Q ∈ π.boxes, x ∉ Q := fun Q hQ hxQ => hx (π.le_of_mem hQ hxQ)
    rw [Set.indicator_of_notMem (show x ∉ (I : Set (Fin d → ℝ)) from hx)]
    exact Finset.sum_eq_zero (fun Q hQ =>
      Set.indicator_of_notMem (show x ∉ (Q : Set (Fin d → ℝ)) from hout Q hQ) g)

/-- Averages on a partition recover a function constant on each box. -/
theorem sum_boxAverage_of_constant {I : Box (Fin d)} (π : Prepartition I)
    (hπ : π.IsPartition) (g : (Fin d → ℝ) → ℝ)
    (hg : ∀ Q ∈ π.boxes, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y) :
    (∑ Q ∈ π.boxes, boxAverage Q g) = (I : Set (Fin d → ℝ)).indicator g := by
  calc
    _ = ∑ Q ∈ π.boxes, (Q : Set (Fin d → ℝ)).indicator g := by
      apply Finset.sum_congr rfl
      intro Q hQ
      exact boxAverage_of_constant Q g (hg Q hQ)
    _ = _ := sum_box_indicators π hπ g

/-- Constancy on the smallest cubes gives integrability, so each average is an
integral of an integrable function. -/
theorem integrableOn_of_leafConstant (I : Box (Fin d)) (N : ℕ)
    (g : (Fin d → ℝ) → ℝ)
    (hg : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y) :
    IntegrableOn g (I : Set (Fin d → ℝ)) volume := by
  rw [← (level_isPartition I N).iUnion_eq, Prepartition.iUnion_def]
  apply integrableOn_finset_iUnion.mpr
  intro Q hQ
  have hc : IntegrableOn (fun _ : Fin d → ℝ => g Q.upper)
      (Q : Set (Fin d → ℝ)) volume :=
    integrableOn_const (Q.measure_coe_lt_top volume).ne
  exact hc.congr_fun (fun x hx => hg Q hQ Q.upper Q.upper_mem x hx) Q.measurableSet_coe

/-- Cancellation between successive dyadic levels. -/
theorem sum_level_difference (I : Box (Fin d)) (n : ℕ) (g : (Fin d → ℝ) → ℝ) :
    (∑ Q ∈ (level I n).boxes, boxDifference Q g) =
      (∑ Q ∈ (level I (n + 1)).boxes, boxAverage Q g) -
        ∑ Q ∈ (level I n).boxes, boxAverage Q g := by
  classical
  simp only [boxDifference, Finset.sum_sub_distrib, level_succ,
    Prepartition.biUnion, Prepartition.sum_biUnion_boxes]

/-- The finite telescope with levels shown explicitly. -/
theorem sum_levels_difference (I : Box (Fin d)) (N : ℕ) (g : (Fin d → ℝ) → ℝ) :
    (∑ n ∈ Finset.range N, ∑ Q ∈ (level I n).boxes, boxDifference Q g) =
      (∑ Q ∈ leaves I N, boxAverage Q g) - boxAverage I g := by
  simp_rw [sum_level_difference]
  convert Finset.sum_range_sub (fun n : ℕ =>
    ∑ Q ∈ (level I n).boxes, boxAverage Q g) N using 1
  simp [leaves]

/-- The telescope with each interior cube appearing once. -/
theorem sum_interior_difference [Nonempty (Fin d)] (I : Box (Fin d)) (N : ℕ)
    (g : (Fin d → ℝ) → ℝ) :
    (∑ Q ∈ interior I N, boxDifference Q g) =
      (∑ Q ∈ leaves I N, boxAverage Q g) - boxAverage I g := by
  rw [sum_interior]
  exact sum_levels_difference I N g

/-- The two one-coordinate telescoping identities. The indices are descendants of the
top cube lying below `P`. Identifying them with descendants of `P` includes the
case where `P` is a smallest cube.

-/
theorem one_coordinate_telescope (d : ℕ) (hd : 0 < d)
    (I : Box (Fin d)) (N : ℕ) (P : Box (Fin d)) (hP : P ∈ descendants I N)
    (g : (Fin d → ℝ) → ℝ)
    (hg : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y) :
    (∑ L ∈ (interior I N).filter (fun L => L ≤ P), boxDifference L g) =
      (∑ Q ∈ (leaves I N).filter (fun Q => Q ≤ P), boxAverage Q g) - boxAverage P g ∧
    (∑ Q ∈ (leaves I N).filter (fun Q => Q ≤ P), boxAverage Q g) - boxAverage P g =
      (P : Set (Fin d → ℝ)).indicator g - boxAverage P g := by
  classical
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨n, hn, hPn⟩ := mem_descendants.mp hP
  rw [← interior_localization hPn hn, ← leaves_localization hPn hn]
  refine ⟨sum_interior_difference P (N - n) g, ?_⟩
  congr 1
  apply sum_boxAverage_of_constant (level P (N - n)) (level_isPartition P (N - n))
  intro Q hQ
  have hglobal : Q ∈ leaves I N := by
    have hlocal : Q ∈ leaves P (N - n) := hQ
    rw [leaves_localization hPn hn] at hlocal
    exact (Finset.mem_filter.mp hlocal).1
  exact hg Q hglobal

end ReyZygmund.Geometry
