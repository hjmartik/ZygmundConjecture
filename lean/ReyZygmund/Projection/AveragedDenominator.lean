import ReyZygmund.Geometry.ProductMaps
import ReyZygmund.Projection.AveragingRectangles

/-! # The rectangle in the averaged denominator

Choose the partition cube containing the selected coordinate of the point. On this
cube, the cross-coordinate average of the other-coordinate averages equals the
full average on the resulting rectangle. Positivity and the maximal-function
comparison are proved in the subsequent estimates.


-/

open BoxIntegral
open scoped Classical

namespace ReyZygmund.Projection

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- The selected partition member supplies the formerly unused coordinate.
Only the other factors of the original tuple must be descendants. -/
theorem update_mem_averagingRectangles
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (j : Fin m) (Q : ∀ i, Box (Fin (d i)))
    (hQ : ∀ i, i ≠ j → Q i ∈ descendants (I i) (N i))
    (P : Box (Fin (d j)))
    (hP : P ∈ partitionCubes (I j) (N j) (eligibleProjections j G Q)) :
    Function.update Q j P ∈ averagingRectangles I N G := by
  have he := eligibleProjections_subset_descendants I N j G Q
    (fun R hR i => mem_productDescendants.mp (hG hR) i)
  have hPd := partitionCubes_subset_descendants he hP
  apply mem_averagingRectangles.mpr
  refine ⟨?_, j, ?_⟩
  · intro i
    by_cases hij : i = j
    · subst i
      simpa using hPd
    · simpa [hij] using hQ i hij
  · simpa only [Function.update_self, eligibleProjections_update] using hP

private theorem productAverageMap_univ_update
    (j : Fin m) (Q : ∀ i, Box (Fin (d i))) (P : Box (Fin (d j))) :
    productAverageMap Finset.univ (Function.update Q j P) =
      averageMap j P * productAverageMap (Finset.univ.erase j) Q := by
  have heq : productAverageMap (Finset.univ.erase j) (Function.update Q j P) =
      productAverageMap (Finset.univ.erase j) Q := by
    apply Finset.noncommProd_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ j)]
  rw [productAverageMap_insert (Finset.univ.erase j) j (by simp),
    Function.update_self, heq]

/-- The selected partition cube identifies the averaged denominator. Other point
coordinates and the unused factor `Q j` are unrestricted. -/
theorem averagedDenominator_eq_productAverage
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (j : Fin m) (Q : ∀ i, Box (Fin (d i))) (P : Box (Fin (d j)))
    (hP : P ∈ partitionCubes (I j) (N j) (eligibleProjections j G Q))
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) (hx : x j ∈ P) :
    coordinateCrossAverage j (I j) (N j) (eligibleProjections j G Q)
      ((productAverageMap (Finset.univ.erase j) Q F).1) x =
        (productAverageMap Finset.univ (Function.update Q j P) F).1 x := by
  have he := eligibleProjections_subset_descendants I N j G Q
    (fun R hR i => mem_productDescendants.mp (hG hR) i)
  rw [productAverageMap_univ_update, Module.End.mul_apply, averageMap_apply,
    coordinateAverage_of_mem j P _ x hx]
  exact finiteCrossAverage_eq_on_partition he _ hP hx

end ReyZygmund.Projection
