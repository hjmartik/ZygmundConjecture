import ReyZygmund.Geometry.ProductAlgebra
import ReyZygmund.Geometry.FiniteCrossAverage

/-! # Cross-coordinate averages on the product space

The eligible projections determine a partition after adjoining all smallest cubes.
The one-coordinate telescoping identities give the corresponding product-space
formulas. The identity for the common projection is proved in
`Projection/CommonProjection.lean`.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- Averaging over a fixed cross-coordinate partition. -/
noncomputable def coordinateCrossAverage (i : Fin m) (I : Box (Fin (d i))) (N : ℕ)
    (eligible : Finset (Box (Fin (d i)))) (f : ProductPoint d → ℝ)
    (x : ProductPoint d) : ℝ :=
  finiteCrossAverage I N eligible (fun y => f (Function.update x i y)) (x i)

theorem coordinateCrossAverage_eq_sum (i : Fin m) (I : Box (Fin (d i))) (N : ℕ)
    (eligible : Finset (Box (Fin (d i)))) (f : ProductPoint d → ℝ) :
    coordinateCrossAverage i I N eligible f =
      ∑ P ∈ partitionCubes I N eligible, coordinateAverage i P f := by
  funext x
  simp only [coordinateCrossAverage, finiteCrossAverage, Finset.sum_apply, coordinateAverage]

theorem coordinateCrossAverage_measurable (i : Fin m) (I : Box (Fin (d i))) (N : ℕ)
    (eligible : Finset (Box (Fin (d i)))) (f : ProductPoint d → ℝ)
    (hf : Measurable f) : Measurable (coordinateCrossAverage i I N eligible f) := by
  rw [coordinateCrossAverage_eq_sum]
  have hs : Measurable (fun x => ∑ P ∈ partitionCubes I N eligible,
      coordinateAverage i P f x) :=
    Finset.measurable_sum _ (fun P _ => coordinateAverage_measurable i P f hf)
  convert hs using 1
  ext x
  simp only [Finset.sum_apply]

theorem coordinateCrossAverage_abs_le (i : Fin m) (I : Box (Fin (d i))) (N : ℕ)
    (eligible : Finset (Box (Fin (d i)))) (he : eligible ⊆ descendants I N)
    (f : ProductPoint d → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ C)
    (x : ProductPoint d) : |coordinateCrossAverage i I N eligible f x| ≤ C := by
  by_cases hx : x i ∈ I
  · obtain ⟨P, hP, hxP⟩ := maximalPartition_isPartition I N eligible he (x i) hx
    have heq : coordinateCrossAverage i I N eligible f x = coordinateAverage i P f x := by
      rw [coordinateAverage_of_mem i P f x hxP]
      exact finiteCrossAverage_eq_on_partition he _ hP hxP
    rw [heq]
    exact coordinateAverage_abs_le i P f C hC hf x
  · change |finiteCrossAverage I N eligible _ (x i)| ≤ C
    rw [finiteCrossAverage_eq_zero_of_notMem he _ hx, abs_zero]
    exact hC

/-- Each slice of the zero-extended finite input is constant on its smallest cubes,
including slices through points outside the top rectangle. -/
theorem productStep_coordinate_leafConstant
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (i : Fin m) (x : ProductPoint d) :
    ∀ Q ∈ leaves (I i) (N i), ∀ y ∈ Q, ∀ z ∈ Q,
      (productBox I).indicator f (Function.update x i y) =
        (productBox I).indicator f (Function.update x i z) := by
  intro Q hQ y hy z hz
  by_cases hxy : Function.update x i y ∈ productBox I
  · obtain ⟨P, hP, hyP⟩ := productLeaves_cover I N _ hxy
    have hPi : P i = Q := (level (I i) (N i)).eq_of_mem_of_mem
      (Fintype.mem_piFinset.mp hP i) hQ
      (by simpa using (mem_productBox P _).mp hyP i) hy
    have hzP : Function.update x i z ∈ productBox P := by
      apply (mem_productBox P _).mpr
      intro j
      by_cases hji : j = i
      · subst j
        simpa [hPi] using hz
      · simpa [hji] using (mem_productBox P _).mp hyP j
    rw [Set.indicator_of_mem hxy, Set.indicator_of_mem (productLeaves_subset hP hzP)]
    exact hf P hP _ hyP _ hzP
  · have hxz : Function.update x i z ∉ productBox I := by
      intro hxz
      apply hxy
      apply (mem_productBox I _).mpr
      intro j
      by_cases hji : j = i
      · subst j
        simpa using (level (I i) (N i)).le_of_mem hQ hy
      · simpa [hji] using (mem_productBox I _).mp hxz j
    simp only [Set.indicator_of_notMem hxy, Set.indicator_of_notMem hxz]

/-- The exact global complement identity for a fixed eligible projection family. -/
theorem coordinateCrossAverage_complement
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (i : Fin m) (hd : 0 < d i) (eligible : Finset (Box (Fin (d i))))
    (he : eligible ⊆ descendants (I i) (N i)) :
    (productBox I).indicator f -
        coordinateCrossAverage i (I i) (N i) eligible ((productBox I).indicator f) =
      ∑ L ∈ (interior (I i) (N i)).filter (fun L => ∃ J ∈ eligible, L ≤ J),
        coordinateDifference i L ((productBox I).indicator f) := by
  funext x
  have ht := congrFun (finiteCrossAverage_complement (d i) hd (I i) (N i) eligible he
    (fun y => (productBox I).indicator f (Function.update x i y))
    (productStep_coordinate_leafConstant I N f hf i x)) (x i)
  have hs : (I i : Set (Fin (d i) → ℝ)).indicator
      (fun y => (productBox I).indicator f (Function.update x i y)) (x i) =
        (productBox I).indicator f x := by
    by_cases hx : x i ∈ I i
    · simp [hx]
    · have hxI : x ∉ productBox I := fun h => hx ((mem_productBox I x).mp h i)
      simp [hx, hxI]
  simpa only [Pi.sub_apply, Finset.sum_apply, hs, coordinateCrossAverage,
    coordinateDifference_slice] using ht

end ReyZygmund.Geometry
