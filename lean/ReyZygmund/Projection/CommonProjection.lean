import ReyZygmund.Geometry.ProductOrthogonality
import ReyZygmund.Geometry.ProductClosure
import ReyZygmund.Projection.FiniteIndices

/-! # The finite common projection

Subtract each selected full product difference once. Applying differences in all
but one coordinate selects the matching removed indices. The one-coordinate
telescoping identity then expresses the result as a cross-coordinate average
of the corresponding difference of the input.
-/

noncomputable section

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Projection

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- The finite expression for the common projection. -/
def finiteProjectionMap (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) : Module.End ℝ (boundedMeasurableFunctions d) :=
  1 - ∑ L ∈ removedIndices I N G, productDifferenceMap Finset.univ L

/-- The cross-coordinate partition average as a linear map. -/
def crossAverageMap (j : Fin m) (I : Box (Fin (d j))) (N : ℕ)
    (eligible : Finset (Box (Fin (d j)))) : Module.End ℝ (boundedMeasurableFunctions d) :=
  ∑ P ∈ partitionCubes I N eligible, averageMap j P

theorem finiteProjectionMap_apply
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (f : boundedMeasurableFunctions d) :
    (finiteProjectionMap I N G f).1 =
      f.1 - ∑ L ∈ removedIndices I N G, (productDifferenceMap Finset.univ L f).1 := by
  funext x
  simp [finiteProjectionMap, Finset.sum_apply]

theorem crossAverageMap_apply
    (j : Fin m) (I : Box (Fin (d j))) (N : ℕ)
    (eligible : Finset (Box (Fin (d j)))) (f : boundedMeasurableFunctions d) :
    (crossAverageMap j I N eligible f).1 = coordinateCrossAverage j I N eligible f.1 := by
  rw [coordinateCrossAverage_eq_sum]
  funext x
  simp [crossAverageMap, Finset.sum_apply]

/-- The exact operator sum before the one-coordinate telescope is applied.
No finiteness condition on the unused factor `K j` is introduced. -/
theorem partialDifference_projectionMap
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (hd : ∀ i, 0 < d i) (G : Finset (∀ i, Box (Fin (d i))))
    (j : Fin m) (K : ∀ i, Box (Fin (d i)))
    (hK : ∀ i, i ≠ j → K i ∈ interior (I i) (N i)) :
    productDifferenceMap (Finset.univ.erase j) K * finiteProjectionMap I N G =
      productDifferenceMap (Finset.univ.erase j) K -
        ∑ Q ∈ selectedCoordinateIndices I N j G K,
          differenceMap j Q * productDifferenceMap (Finset.univ.erase j) K := by
  have hdist :
      productDifferenceMap (Finset.univ.erase j) K * finiteProjectionMap I N G =
        productDifferenceMap (Finset.univ.erase j) K -
          ∑ L ∈ removedIndices I N G,
            productDifferenceMap (Finset.univ.erase j) K *
              productDifferenceMap Finset.univ L := by
    apply LinearMap.ext
    intro v
    simp only [finiteProjectionMap, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_sub, map_sum, LinearMap.sum_apply]
  rw [hdist]
  congr 1
  calc
    _ = ∑ L ∈ removedIndices I N G,
        if ∀ i, i ≠ j → L i = K i then
          differenceMap j (L j) * productDifferenceMap (Finset.univ.erase j) K else 0 := by
      apply Finset.sum_congr rfl
      intro L hL
      apply productDifferenceMap_mul_full_erase I N hd j K L
      · intro i hij
        exact interior_subset_descendants (I i) (N i) (hK i hij)
      · intro i
        exact interior_subset_descendants (I i) (N i)
          ((mem_productInterior.mp (Finset.mem_filter.mp hL).1) i)
    _ = _ := sum_removedIndices_fiber I N j G K hK
      (fun Q => differenceMap j Q * productDifferenceMap (Finset.univ.erase j) K)

theorem partialDifference_projection_apply
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (hd : ∀ i, 0 < d i) (G : Finset (∀ i, Box (Fin (d i))))
    (j : Fin m) (K : ∀ i, Box (Fin (d i)))
    (hK : ∀ i, i ≠ j → K i ∈ interior (I i) (N i))
    (f : boundedMeasurableFunctions d) :
    productDifferenceMap (Finset.univ.erase j) K (finiteProjectionMap I N G f) =
      productDifferenceMap (Finset.univ.erase j) K f -
        ∑ Q ∈ selectedCoordinateIndices I N j G K,
          differenceMap j Q (productDifferenceMap (Finset.univ.erase j) K f) := by
  have ht := congrArg (fun T : Module.End ℝ (boundedMeasurableFunctions d) => T f)
    (partialDifference_projectionMap I N hd G j K hK)
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.sum_apply] using ht

/-- The cross-coordinate identity is a pointwise equality of functions after
restricting the input to the top rectangle. Incomparability is not required.
-/
theorem finite_cross_projection
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (hd : ∀ i, 0 < d i) (G : Finset (∀ i, Box (Fin (d i))))
    (hG : ∀ J ∈ G, ∀ i, J i ∈ descendants (I i) (N i))
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (j : Fin m) (K : ∀ i, Box (Fin (d i)))
    (hK : ∀ i, i ≠ j → K i ∈ interior (I i) (N i)) :
    (productDifferenceMap (Finset.univ.erase j) K
      (finiteProjectionMap I N G (finiteInput I N f hf))).1 =
        coordinateCrossAverage j (I j) (N j) (eligibleProjections j G K)
          (productDifferenceMap (Finset.univ.erase j) K (finiteInput I N f hf)).1 := by
  let u := finiteInput I N f hf
  let g := productDifferenceMap (Finset.univ.erase j) K u
  have hu : ProductLeafConstant I N u.1 := productLeafConstant_indicator hf
  have hus : ∀ x, x ∉ productBox I → u.1 x = 0 := by
    intro x hx
    exact Set.indicator_of_notMem hx f
  have hg := productDifferenceMap_productStep_closure I N u hu hus
    (Finset.univ.erase j) K (fun i hi => hK i (Finset.mem_erase.mp hi).1)
  have hsupport : (productBox I).indicator g.1 = g.1 := by
    funext x
    by_cases hx : x ∈ productBox I
    · exact Set.indicator_of_mem hx g.1
    · rw [Set.indicator_of_notMem hx, hg.2 x hx]
  have hc := coordinateCrossAverage_complement I N g.1 hg.1 j (hd j)
    (eligibleProjections j G K) (eligibleProjections_subset_descendants I N j G K hG)
  rw [hsupport] at hc
  have hsum : g.1 - coordinateCrossAverage j (I j) (N j) (eligibleProjections j G K) g.1 =
      ∑ Q ∈ selectedCoordinateIndices I N j G K, coordinateDifference j Q g.1 := by
    simpa only [selectedCoordinateIndices_eq_filter I N j G K] using hc
  have hv := congrArg (fun v : boundedMeasurableFunctions d => v.1)
    (partialDifference_projection_apply I N hd G j K hK u)
  have hvalue : (productDifferenceMap (Finset.univ.erase j) K
      (finiteProjectionMap I N G u)).1 =
        g.1 - ∑ Q ∈ selectedCoordinateIndices I N j G K, coordinateDifference j Q g.1 := by
    simpa only [AddSubgroupClass.coe_sub, Submodule.coe_sum, differenceMap_apply] using hv
  change (productDifferenceMap (Finset.univ.erase j) K (finiteProjectionMap I N G u)).1 =
    coordinateCrossAverage j (I j) (N j) (eligibleProjections j G K) g.1
  rw [hvalue, ← hsum, sub_sub_cancel]

end ReyZygmund.Projection
