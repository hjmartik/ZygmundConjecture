import ReyZygmund.MathlibOnly.Projections
import ReyZygmund.Geometry.ProductFiniteSetting
import ReyZygmund.Projection.FiniteIndices

/-! # The finite cross-coordinate partition

The public candidates are the eligible projections together with every smallest
cube. Taking maximal members therefore gives the actual finite partition used
in the telescoping argument. Completing the partial rectangle with the top cube
in the omitted coordinate does not change eligibility.
-/

noncomputable section

open BoxIntegral
open scoped BigOperators Classical

namespace ReyZygmund.Projection

open Geometry
open MathlibOnly (CubeGrid Rectangle PartialRectangle)

variable {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, CubeGrid (d i))
    {I : Rectangle d} {l : Fin m → ℤ} {k : ℤ}
    (hI : ∀ i, I i ∈ (D i).cubes (l i)) (hcut : ∀ i, -k ≤ l i)

include hI hcut

/-- The public candidate set is the finite union of eligible projections and
smallest cubes. Each projected cube occurs only once. -/
theorem crossCandidates_eq_eligibleProjections_union_leaves
    (G : Finset (Rectangle d)) (j : Fin m)
    (K : PartialRectangle d (Finset.univ.erase j)) :
    MathlibOnly.crossCandidates D I k (G : Set (Rectangle d)) j K =
      ((eligibleProjections j G (completePartialRectangle I (Finset.univ.erase j) K) ∪
        leaves (I j) (l j + k).toNat : Finset (Box (Fin (d j)))) : Set (Box (Fin (d j)))) := by
  rw [MathlibOnly.crossCandidates, bottomCubes_eq_leaves (D j) (hI j) (hcut j)]
  ext P
  simp only [Set.mem_union, Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_union]
  apply or_congr_left
  simp only [eligibleProjections, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨R, hR, rfl, hKR⟩
    refine ⟨R, ⟨hR, ?_⟩, rfl⟩
    intro i hij
    have hi : i ∈ (Finset.univ.erase j : Finset (Fin m)) :=
      Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
    simpa only [completePartialRectangle, dite_eq_left hi, Box.coe_subset_coe] using hKR ⟨i, hi⟩
  · rintro ⟨R, ⟨hR, hKR⟩, hRP⟩
    refine ⟨R, hR, hRP.symm, ?_⟩
    intro i
    simpa only [completePartialRectangle_selected, Box.coe_subset_coe] using
      hKR i (Finset.mem_erase.mp i.property).1

/-- The public maximal candidate set is precisely the finite maximal partition. -/
theorem crossPartition_eq_partitionCubes
    (G : Finset (Rectangle d)) (j : Fin m)
    (K : PartialRectangle d (Finset.univ.erase j)) :
    MathlibOnly.crossPartition D I k (G : Set (Rectangle d)) j K =
      (partitionCubes (I j) (l j + k).toNat
        (eligibleProjections j G (completePartialRectangle I (Finset.univ.erase j) K)) :
          Set (Box (Fin (d j)))) := by
  ext P
  simp only [MathlibOnly.crossPartition,
    crossCandidates_eq_eligibleProjections_union_leaves D hI hcut G j K,
    Set.mem_ofPred_eq, Finset.mem_coe, partitionCubes, mem_maximalCubes, Maximal]

/-- The public real-valued sum is the finite coordinate partition average.
This equality holds for arbitrary inputs at every point. -/
theorem crossAverage_eq_coordinateCrossAverage
    (G : Finset (Rectangle d)) (j : Fin m)
    (K : PartialRectangle d (Finset.univ.erase j)) (g : MathlibOnly.ProductPoint d → ℝ) :
    MathlibOnly.crossAverage D I k (G : Set (Rectangle d)) j K g =
      coordinateCrossAverage j (I j) (l j + k).toNat
        (eligibleProjections j G (completePartialRectangle I (Finset.univ.erase j) K)) g := by
  rw [coordinateCrossAverage_eq_sum]
  funext x
  rw [MathlibOnly.crossAverage, crossPartition_eq_partitionCubes D hI hcut G j K]
  simp only [Finset.sum_apply]
  exact Finset.tsum_subtype' _ (fun P => MathlibOnly.coordinateAverage j P g x)

end ReyZygmund.Projection
