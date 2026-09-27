import ReyZygmund.Projection.Properties
import ReyZygmund.Projection.AveragingRectangles

/-!
# Averages preserved by the finite projection

For the averaging family, maximality of one partition cube rules out a
removed difference strictly above the averaging rectangle in every coordinate.
The same argument on the original family only needs the weaker containment
condition of source Section 6, rather than incomparability.
-/

noncomputable section

open BoxIntegral
open scoped BigOperators Classical

namespace ReyZygmund.Projection

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem preserves_average_of_removed_indices
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (R : ∀ i, Box (Fin (d i)))
    (hR : ∀ i, R i ∈ descendants (I i) (N i))
    (havoid : ∀ L ∈ removedIndices I N G, ∃ i, ¬ R i < L i) :
    productAverageMap Finset.univ R * finiteProjectionMap I N G =
      productAverageMap Finset.univ R := by
  have hzero : (∑ L ∈ removedIndices I N G,
      productAverageMap Finset.univ R * productDifferenceMap Finset.univ L) = 0 := by
    apply Finset.sum_eq_zero
    intro L hL
    obtain ⟨i, hi⟩ := havoid L hL
    apply productAverageMap_mul_full_difference_eq_zero I N Finset.univ R L
      (fun j _ => hR j)
    · intro j
      exact interior_subset_descendants (I j) (N j)
        ((mem_productInterior.mp (Finset.mem_filter.mp hL).1) j)
    · exact ⟨i, Finset.mem_univ i, hd i, hi⟩
  calc
    _ = productAverageMap Finset.univ R -
        ∑ L ∈ removedIndices I N G,
          productAverageMap Finset.univ R * productDifferenceMap Finset.univ L := by
      apply LinearMap.ext
      intro f
      simp only [finiteProjectionMap, Module.End.mul_apply, LinearMap.sub_apply,
        Module.End.one_apply, map_sub, map_sum, LinearMap.sum_apply]
    _ = _ := by
      rw [hzero]
      apply LinearMap.ext
      intro f
      simp

/-- The common projection preserves averages on the averaging family, without
incomparability. -/
theorem averagingRectangles_preserved
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (R : ∀ i, Box (Fin (d i)))
    (hR : R ∈ averagingRectangles I N G) :
    productAverageMap Finset.univ R * finiteProjectionMap I N G =
      productAverageMap Finset.univ R := by
  obtain ⟨hRd, j, hRj⟩ := mem_averagingRectangles.mp hR
  apply preserves_average_of_removed_indices I N hd G R hRd
  intro L hL
  obtain ⟨_, J, hJ, hLJ⟩ := Finset.mem_filter.mp hL
  by_contra! hstrict
  have hJe : J j ∈ eligibleProjections j G R := by
    apply Finset.mem_image.mpr
    exact ⟨J, Finset.mem_filter.mpr ⟨hJ, fun i _ => (hstrict i).le.trans (hLJ i)⟩, rfl⟩
  have hRJ : R j < J j := lt_of_lt_of_le (hstrict j) (hLJ j)
  have hJR : J j ≤ R j := (mem_maximalCubes.mp hRj).2 (J j)
    (Finset.mem_union_left _ hJe) hRJ.le
  exact (not_lt_of_ge hJR) hRJ

/-- Original averages are also preserved under the weaker containment
condition used later in the paper, without asserting original membership in
the averaging family. -/
theorem original_averages_preserved_of_weaker_containment
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : ∀ R ∈ G, ∀ J ∈ G, ¬ ∀ i, R i < J i)
    (R : ∀ i, Box (Fin (d i))) (hR : R ∈ G) :
    productAverageMap Finset.univ R * finiteProjectionMap I N G =
      productAverageMap Finset.univ R := by
  apply preserves_average_of_removed_indices I N hd G R
    (mem_productDescendants.mp (hG hR))
  intro L hL
  obtain ⟨_, J, hJ, hLJ⟩ := Finset.mem_filter.mp hL
  by_contra! hstrict
  exact hweak R hR J hJ (fun i => lt_of_lt_of_le (hstrict i) (hLJ i))

end ReyZygmund.Projection
