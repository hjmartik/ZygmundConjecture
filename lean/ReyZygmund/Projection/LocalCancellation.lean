import ReyZygmund.Projection.PreservedAverages

/-! # Cancellation below an averaging rectangle

The partition-index identity applies both to original projections and inserted
smallest cubes. Thus each interior full index below an averaging rectangle is
already removed by the projection, and its difference vanishes.
`LocalProductExpansion.lean` supplies the telescoping expansion used with this
cancellation.

-/

open BoxIntegral
open scoped BigOperators Classical

namespace ReyZygmund.Projection

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- An interior index below an averaging rectangle is removed by the projection.
The partition-index equality includes the case of an inserted cutoff cube. -/
theorem interior_below_averagingRectangle_removed
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (R : ∀ i, Box (Fin (d i)))
    (hR : R ∈ averagingRectangles I N G) (L : ∀ i, Box (Fin (d i)))
    (hL : L ∈ productInterior I N) (hLR : ∀ i, L i ≤ R i) :
    L ∈ removedIndices I N G := by
  obtain ⟨_, j, hRj⟩ := mem_averagingRectangles.mp hR
  let : Nonempty (Fin (d j)) := ⟨⟨0, hd j⟩⟩
  have hLj : L j ∈ (interior (I j) (N j)).filter
      (fun Q => ∃ P ∈ partitionCubes (I j) (N j) (eligibleProjections j G R), Q ≤ P) :=
    Finset.mem_filter.mpr ⟨mem_productInterior.mp hL j, R j, hRj, hLR j⟩
  rw [← partition_indices (I j) (N j) (eligibleProjections j G R)] at hLj
  obtain ⟨_, P, hP, hLP⟩ := Finset.mem_filter.mp hLj
  obtain ⟨J, hJ, hJP⟩ := Finset.mem_image.mp hP
  obtain ⟨hJG, hRJ⟩ := Finset.mem_filter.mp hJ
  apply Finset.mem_filter.mpr
  refine ⟨hL, J, hJG, ?_⟩
  intro i
  by_cases hij : i = j
  · subst i
    simpa only [hJP] using hLP
  · exact (hLR i).trans (hRJ i hij)

/-- The full difference sum below an averaging rectangle vanishes on the
projected input. This is an operator identity, including an empty index sum. -/
theorem averagingRectangle_difference_sum_vanishes
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (R : ∀ i, Box (Fin (d i)))
    (hR : R ∈ averagingRectangles I N G) :
    (∑ L ∈ (productInterior I N).filter (fun L => ∀ i, L i ≤ R i),
      productDifferenceMap Finset.univ L * finiteProjectionMap I N G) = 0 := by
  apply Finset.sum_eq_zero
  intro L hL
  obtain ⟨hLi, hLR⟩ := Finset.mem_filter.mp hL
  exact productDifferenceMap_mul_finiteProjectionMap I N hd G L
    (interior_below_averagingRectangle_removed I N hd G R hR L hLi hLR)

end ReyZygmund.Projection
