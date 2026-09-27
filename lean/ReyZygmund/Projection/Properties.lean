import ReyZygmund.Projection.CommonProjection
import ReyZygmund.Geometry.AverageDifferenceMaps

/-! # Properties of the finite common projection

The projection preserves top-cube coordinate averages, annihilates each removed
full difference, and preserves constancy on the smallest cubes.
`GridProjection.lean` identifies this finite expression with the input
minus the removed-difference sum over the full grids.

-/

noncomputable section

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Projection

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem removed_coordinate_mem
    {I : ∀ i, Box (Fin (d i))} {N : Fin m → ℕ}
    {G : Finset (∀ i, Box (Fin (d i)))} {L : ∀ i, Box (Fin (d i))}
    (hL : L ∈ removedIndices I N G) (i : Fin m) :
    L i ∈ descendants (I i) (N i) :=
  interior_subset_descendants (I i) (N i)
    ((mem_productInterior.mp (Finset.mem_filter.mp hL).1) i)

private theorem map_mul_finiteProjectionMap
    (T : Module.End ℝ (boundedMeasurableFunctions d))
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) :
    T * finiteProjectionMap I N G =
      T - ∑ L ∈ removedIndices I N G, T * productDifferenceMap Finset.univ L := by
  apply LinearMap.ext
  intro f
  simp only [finiteProjectionMap, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.one_apply, map_sub, map_sum, LinearMap.sum_apply]

/-- The finite projection preserves the top-cube coordinate averages. -/
theorem averageMap_mul_finiteProjectionMap
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (i : Fin m) (hd : 0 < d i) :
    averageMap i (I i) * finiteProjectionMap I N G = averageMap i (I i) := by
  rw [map_mul_finiteProjectionMap]
  have hzero : (∑ L ∈ removedIndices I N G,
      averageMap i (I i) * productDifferenceMap Finset.univ L) = 0 := by
    apply Finset.sum_eq_zero
    intro L hL
    apply averageMap_mul_productDifferenceMap_eq_zero I N Finset.univ i
      (Finset.mem_univ i) hd (I i) L
    · exact mem_descendants.mpr ⟨0, Nat.zero_le _, Prepartition.mem_top.mpr rfl⟩
    · exact removed_coordinate_mem hL i
    · exact not_lt_of_ge (le_of_mem_descendants (removed_coordinate_mem hL i))
  rw [hzero]
  apply LinearMap.ext
  intro f
  simp

/-- Every removed finite full difference is annihilated, with no multiplicity. -/
theorem productDifferenceMap_mul_finiteProjectionMap
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (hd : ∀ i, 0 < d i) (G : Finset (∀ i, Box (Fin (d i))))
    (K : ∀ i, Box (Fin (d i))) (hK : K ∈ removedIndices I N G) :
    productDifferenceMap Finset.univ K * finiteProjectionMap I N G = 0 := by
  rw [map_mul_finiteProjectionMap]
  have hsum : (∑ L ∈ removedIndices I N G,
      productDifferenceMap Finset.univ K * productDifferenceMap Finset.univ L) =
        productDifferenceMap Finset.univ K := by
    calc
      _ = ∑ L ∈ removedIndices I N G,
          if K = L then productDifferenceMap Finset.univ L else 0 := by
        apply Finset.sum_congr rfl
        intro L hL
        rw [productDifferenceMap_mul_full I N hd Finset.univ K L
          (fun i _ => removed_coordinate_mem hK i) (removed_coordinate_mem hL)]
        congr 1
        exact propext ⟨fun h => funext (fun i => h i (Finset.mem_univ i)),
          fun h i _ => congrFun h i⟩
      _ = _ := by simp [hK]
  rw [hsum]
  apply LinearMap.ext
  intro f
  simp

/-- Subtracting the finite differences preserves the finite step input. -/
theorem finiteProjectionMap_productStep_closure
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (f : boundedMeasurableFunctions d)
    (hf : ProductLeafConstant I N f.1)
    (hs : ∀ x, x ∉ productBox I → f.1 x = 0) :
    ProductLeafConstant I N (finiteProjectionMap I N G f).1 ∧
      ∀ x, x ∉ productBox I → (finiteProjectionMap I N G f).1 x = 0 := by
  have hterm : ∀ L ∈ removedIndices I N G,
      ProductLeafConstant I N (productDifferenceMap Finset.univ L f).1 ∧
        ∀ x, x ∉ productBox I → (productDifferenceMap Finset.univ L f).1 x = 0 := by
    intro L hL
    exact productDifferenceMap_productStep_closure I N f hf hs Finset.univ L
      (fun i _ => (mem_productInterior.mp (Finset.mem_filter.mp hL).1) i)
  rw [finiteProjectionMap_apply]
  constructor
  · apply productLeafConstant_sub hf
    exact productLeafConstant_finsetSum _ _ (fun L hL => (hterm L hL).1)
  · intro x hx
    simp only [Pi.sub_apply, Finset.sum_apply, hs x hx]
    have hz : (∑ L ∈ removedIndices I N G,
        (productDifferenceMap Finset.univ L f).1 x) = 0 :=
      Finset.sum_eq_zero (fun L hL => (hterm L hL).2 x hx)
    rw [hz, sub_self]

end ReyZygmund.Projection
