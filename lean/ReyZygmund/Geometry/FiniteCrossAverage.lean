import ReyZygmund.Geometry.FiniteAverages
import ReyZygmund.Geometry.FinitePartition

/-! # Averaging over the cross-coordinate partition

Adjoin all smallest cubes to the eligible projections, select the maximal cubes,
and sum their supported averages. This defines the one-coordinate operator used
for cross-coordinate averages. Its relation to projected martingale differences is
proved in `Projection/CommonProjection.lean`.

-/

noncomputable section

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

variable {d : ℕ}

/-- The cross-coordinate average for a fixed finite family of eligible projections. -/
def finiteCrossAverage (I : Box (Fin d)) (N : ℕ) (eligible : Finset (Box (Fin d)))
    (g : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  ∑ P ∈ partitionCubes I N eligible, boxAverage P g

namespace CrossAverage

theorem measurable_boxAverage (Q : Box (Fin d)) (g : (Fin d → ℝ) → ℝ) :
    Measurable (boxAverage Q g) := by
  exact measurable_const.indicator Q.measurableSet_coe

theorem integrable_boxAverage (Q : Box (Fin d)) (g : (Fin d → ℝ) → ℝ) :
    Integrable (boxAverage Q g) volume := by
  exact (integrableOn_const (Q.measure_coe_lt_top volume).ne).integrable_indicator
    Q.measurableSet_coe

theorem integral_boxAverage (Q : Box (Fin d)) (g : (Fin d → ℝ) → ℝ) :
    (∫ x, boxAverage Q g x) = ∫ x in (Q : Set (Fin d → ℝ)), g x := by
  rw [boxAverage, integral_indicator_const _ Q.measurableSet_coe, smul_eq_mul]
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt (box_volume_pos Q))]

end CrossAverage

theorem finiteCrossAverage_measurable (I : Box (Fin d)) (N : ℕ)
    (eligible : Finset (Box (Fin d))) (g : (Fin d → ℝ) → ℝ) :
    Measurable (finiteCrossAverage I N eligible g) := by
  change Measurable (fun x => finiteCrossAverage I N eligible g x)
  simpa only [finiteCrossAverage, Finset.sum_apply] using
    (partitionCubes I N eligible).measurable_sum
      (fun P _ => CrossAverage.measurable_boxAverage P g)

theorem finiteCrossAverage_integrable (I : Box (Fin d)) (N : ℕ)
    (eligible : Finset (Box (Fin d))) (g : (Fin d → ℝ) → ℝ) :
    Integrable (finiteCrossAverage I N eligible g) volume :=
  integrable_finsetSum' _ (fun P _ => CrossAverage.integrable_boxAverage P g)

/-- The averaged function vanishes outside the top cube. -/
theorem finiteCrossAverage_eq_zero_of_notMem {I : Box (Fin d)} {N : ℕ}
    {eligible : Finset (Box (Fin d))} (he : eligible ⊆ descendants I N)
    (g : (Fin d → ℝ) → ℝ) {x : Fin d → ℝ} (hx : x ∉ I) :
    finiteCrossAverage I N eligible g x = 0 := by
  simp only [finiteCrossAverage, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro P hP
  have hxP : x ∉ P :=
    fun h => hx (le_of_mem_descendants (partitionCubes_subset_descendants he hP) h)
  simp [boxAverage, hxP]

/-- Integrability on the top cube suffices to preserve its integral; values outside
the cube are unrestricted. -/
theorem finiteCrossAverage_integral {I : Box (Fin d)} {N : ℕ}
    {eligible : Finset (Box (Fin d))} (he : eligible ⊆ descendants I N)
    (g : (Fin d → ℝ) → ℝ) (hg : IntegrableOn g (I : Set (Fin d → ℝ)) volume) :
    (∫ x, finiteCrossAverage I N eligible g x) = ∫ x in (I : Set (Fin d → ℝ)), g x := by
  have hIndicators : ∀ P ∈ partitionCubes I N eligible,
      Integrable ((P : Set (Fin d → ℝ)).indicator g) volume := by
    intro P hP
    exact (hg.mono_set (le_of_mem_descendants
      (partitionCubes_subset_descendants he hP))).integrable_indicator P.measurableSet_coe
  have hsum : (∑ P ∈ partitionCubes I N eligible, (P : Set (Fin d → ℝ)).indicator g) =
      (I : Set (Fin d → ℝ)).indicator g :=
    sum_box_indicators (maximalPartition I N eligible he)
      (maximalPartition_isPartition I N eligible he) g
  calc
    (∫ x, finiteCrossAverage I N eligible g x) =
        ∑ P ∈ partitionCubes I N eligible, ∫ x, boxAverage P g x := by
      simp only [finiteCrossAverage, Finset.sum_apply]
      exact integral_finsetSum _ (fun P _ => CrossAverage.integrable_boxAverage P g)
    _ = ∑ P ∈ partitionCubes I N eligible, ∫ x in (P : Set (Fin d → ℝ)), g x := by
      exact Finset.sum_congr rfl (fun P _ => CrossAverage.integral_boxAverage P g)
    _ = ∫ x, (∑ P ∈ partitionCubes I N eligible,
        (P : Set (Fin d → ℝ)).indicator g) x := by
      simp only [Finset.sum_apply]
      rw [integral_finsetSum _ hIndicators]
      exact Finset.sum_congr rfl (fun P _ => (integral_indicator P.measurableSet_coe).symm)
    _ = ∫ x in (I : Set (Fin d → ℝ)), g x := by
      rw [hsum, integral_indicator I.measurableSet_coe]

/-- On a partition cube, the output is its constant average. -/
theorem finiteCrossAverage_eq_on_partition {I P : Box (Fin d)} {N : ℕ}
    {eligible : Finset (Box (Fin d))} (he : eligible ⊆ descendants I N)
    (g : (Fin d → ℝ) → ℝ) (hP : P ∈ partitionCubes I N eligible)
    {x : Fin d → ℝ} (hx : x ∈ P) :
    finiteCrossAverage I N eligible g x =
      (∫ y in (P : Set (Fin d → ℝ)), g y) / volume.real (P : Set (Fin d → ℝ)) := by
  simp only [finiteCrossAverage, Finset.sum_apply]
  rw [Finset.sum_eq_single P]
  · simp [boxAverage, hx]
  · intro Q hQ hQP
    have hxQ : x ∉ Q := fun h =>
      hQP ((maximalPartition I N eligible he).eq_of_mem_of_mem hQ hP h hx)
    simp [boxAverage, hxQ]
  · simp [hP]

/-- Every smallest cube lies in a maximal cube, so the output is constant on each smallest cube. -/
theorem finiteCrossAverage_leafConstant {I : Box (Fin d)} {N : ℕ}
    {eligible : Finset (Box (Fin d))} (he : eligible ⊆ descendants I N)
    (g : (Fin d → ℝ) → ℝ) :
    ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q,
      finiteCrossAverage I N eligible g x = finiteCrossAverage I N eligible g y := by
  intro Q hQ x hx y hy
  obtain ⟨P, hP, hQP⟩ := exists_maximal_supercube (Finset.mem_union_right eligible hQ)
  exact (finiteCrossAverage_eq_on_partition he g hP (hQP hx)).trans
    (finiteCrossAverage_eq_on_partition he g hP (hQP hy)).symm

private theorem sum_partition_descendants {M : Type*} [AddCommMonoid M]
    {I : Box (Fin d)} {N : ℕ} {eligible : Finset (Box (Fin d))}
    (he : eligible ⊆ descendants I N) (f : Box (Fin d) → M) :
    (∑ P ∈ partitionCubes I N eligible,
      ∑ L ∈ (interior I N).filter (fun L => L ≤ P), f L) =
      ∑ L ∈ (interior I N).filter (fun L => ∃ P ∈ partitionCubes I N eligible, L ≤ P),
        f L := by
  have hunion : (partitionCubes I N eligible).biUnion
      (fun P => (interior I N).filter (fun L => L ≤ P)) =
      (interior I N).filter (fun L => ∃ P ∈ partitionCubes I N eligible, L ≤ P) := by
    ext L
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨P, hP, hL, hLP⟩
      exact ⟨hL, P, hP, hLP⟩
    · rintro ⟨hL, P, hP, hLP⟩
      exact ⟨P, hP, hL, hLP⟩
  rw [← hunion]
  symm
  apply Finset.sum_biUnion
  intro P hP Q hQ hPQ
  apply Finset.disjoint_left.mpr
  intro L hLP hLQ
  exact hPQ ((maximalPartition I N eligible he).eq_of_le_of_le hP hQ
    (Finset.mem_filter.mp hLP).2 (Finset.mem_filter.mp hLQ).2)

/-- The exact pointwise complement identity used in the proof of `lem:cross`.
This theorem acts in one coordinate and does not assert the product projection identity. -/
theorem finiteCrossAverage_complement (d : ℕ) (hd : 0 < d)
    (I : Box (Fin d)) (N : ℕ) (eligible : Finset (Box (Fin d)))
    (he : eligible ⊆ descendants I N) (g : (Fin d → ℝ) → ℝ)
    (hg : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y) :
    (I : Set (Fin d → ℝ)).indicator g - finiteCrossAverage I N eligible g =
      ∑ L ∈ (interior I N).filter (fun L => ∃ J ∈ eligible, L ≤ J), boxDifference L g := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hsum := sum_box_indicators (maximalPartition I N eligible he)
    (maximalPartition_isPartition I N eligible he) g
  calc
    (I : Set (Fin d → ℝ)).indicator g - finiteCrossAverage I N eligible g =
        (∑ P ∈ partitionCubes I N eligible, (P : Set (Fin d → ℝ)).indicator g) -
          ∑ P ∈ partitionCubes I N eligible, boxAverage P g :=
      congrArg (fun f => f - finiteCrossAverage I N eligible g) hsum.symm
    _ = ∑ P ∈ partitionCubes I N eligible,
        ((P : Set (Fin d → ℝ)).indicator g - boxAverage P g) := by
      rw [Finset.sum_sub_distrib]
    _ = ∑ P ∈ partitionCubes I N eligible,
        ∑ L ∈ (interior I N).filter (fun L => L ≤ P), boxDifference L g := by
      apply Finset.sum_congr rfl
      intro P hP
      have ht := one_coordinate_telescope d hd I N P
        (partitionCubes_subset_descendants he hP) g hg
      exact (ht.1.trans ht.2).symm
    _ = ∑ L ∈ (interior I N).filter
        (fun L => ∃ P ∈ partitionCubes I N eligible, L ≤ P), boxDifference L g :=
      sum_partition_descendants he (fun L => boxDifference L g)
    _ = ∑ L ∈ (interior I N).filter (fun L => ∃ J ∈ eligible, L ≤ J),
        boxDifference L g := by rw [partition_indices I N eligible]

/-- If no original projection is eligible, the partition consists of the inserted smallest cubes. -/
theorem finiteCrossAverage_empty (I : Box (Fin d)) (N : ℕ) (g : (Fin d → ℝ) → ℝ)
    (hg : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y) :
    finiteCrossAverage I N ∅ g = (I : Set (Fin d → ℝ)).indicator g := by
  unfold finiteCrossAverage
  rw [partitionCubes_empty]
  exact sum_boxAverage_of_constant (level I N) (level_isPartition I N) g hg

/-- Depth zero has a single averaging cube, whether or not it was originally eligible. -/
theorem finiteCrossAverage_zero_depth (I : Box (Fin d)) (eligible : Finset (Box (Fin d)))
    (he : eligible ⊆ descendants I 0) (g : (Fin d → ℝ) → ℝ) :
    finiteCrossAverage I 0 eligible g = boxAverage I g := by
  have heleaf : eligible ⊆ leaves I 0 := by
    intro P hP
    obtain ⟨n, hn, hPn⟩ := mem_descendants.mp (he hP)
    have hn0 : n = 0 := by omega
    subst n
    exact hPn
  simp only [finiteCrossAverage, partitionCubes_eq_leaves_of_subset heleaf,
    leaves_zero, Finset.sum_singleton]

/-- If the top cube is eligible, the partition operator is its supported average. -/
theorem finiteCrossAverage_of_root_mem {I : Box (Fin d)} {N : ℕ}
    {eligible : Finset (Box (Fin d))} (he : eligible ⊆ descendants I N) (hI : I ∈ eligible)
    (g : (Fin d → ℝ) → ℝ) : finiteCrossAverage I N eligible g = boxAverage I g := by
  have hIm : I ∈ partitionCubes I N eligible := by
    apply mem_maximalCubes.mpr
    refine ⟨Finset.mem_union_left _ hI, ?_⟩
    intro P hP _
    apply le_of_mem_descendants
    rcases Finset.mem_union.mp hP with hPe | hPl
    · exact he hPe
    · exact leaves_subset_descendants I N hPl
  funext x
  by_cases hx : x ∈ I
  · simpa [boxAverage, hx] using
      finiteCrossAverage_eq_on_partition he g hIm hx
  · rw [finiteCrossAverage_eq_zero_of_notMem he g hx]
    simp [boxAverage, hx]

/-- The one-coordinate cross-average and complement identities. Constancy of the input
on the smallest cubes implies local integrability, measurability and integrability
of the output, preservation of the integral, and the pointwise complement formula.



-/
theorem finite_cross_average (d : ℕ) (hd : 0 < d) (I : Box (Fin d)) (N : ℕ)
    (eligible : Finset (Box (Fin d))) (he : eligible ⊆ descendants I N)
    (g : (Fin d → ℝ) → ℝ)
    (hg : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y) :
    IntegrableOn g (I : Set (Fin d → ℝ)) volume ∧
      Measurable (finiteCrossAverage I N eligible g) ∧
      Integrable (finiteCrossAverage I N eligible g) volume ∧
      (∫ x, finiteCrossAverage I N eligible g x) = (∫ x in (I : Set (Fin d → ℝ)), g x) ∧
      (I : Set (Fin d → ℝ)).indicator g - finiteCrossAverage I N eligible g =
        ∑ L ∈ (interior I N).filter (fun L => ∃ J ∈ eligible, L ≤ J), boxDifference L g := by
  have hgi := integrableOn_of_leafConstant I N g hg
  exact ⟨hgi, finiteCrossAverage_measurable I N eligible g,
    finiteCrossAverage_integrable I N eligible g, finiteCrossAverage_integral he g hgi,
    finiteCrossAverage_complement d hd I N eligible he g hg⟩

end ReyZygmund.Geometry
