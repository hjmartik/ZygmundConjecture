import ReyZygmund.Geometry.ProductOrthogonality

/-! # Vanishing averages of product differences

The one-coordinate average–difference cancellation holds on bounded measurable
functions. Extracting one average and one difference gives the product
cancellation used to preserve rectangle averages.


-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- Same-coordinate cancellation, assuming integrability on the relevant slice of the top rectangle. -/
theorem coordinateAverage_difference_eq_zero
    (i : Fin m) (hd : 0 < d i) (I : Box (Fin (d i))) (N : ℕ)
    (K L : Box (Fin (d i))) (hK : K ∈ descendants I N) (hL : L ∈ descendants I N)
    (hnot : ¬ K < L) (f : ProductPoint d → ℝ)
    (hf : ∀ x, IntegrableOn (fun y => f (Function.update x i y))
      (I : Set (Fin (d i) → ℝ)) volume) :
    coordinateAverage i K (coordinateDifference i L f) = 0 := by
  funext x
  have hs : (fun y => coordinateDifference i L f (Function.update x i y)) =
      boxDifference L (fun y => f (Function.update x i y)) := by
    funext y
    simp [coordinateDifference_slice]
  change boxAverage K (fun y => coordinateDifference i L f (Function.update x i y))
    (x i) = 0
  rw [hs]
  have ht := congrFun (finite_average_difference (d i) hd I N K L hK hL
    (fun y => f (Function.update x i y)) (hf x)) (x i)
  simpa [hnot] using ht

/-- The same-coordinate zero branch on the existing concrete function space.
Equality of the cubes belongs to this branch, as do ancestors and disjoint cubes. -/
theorem averageMap_mul_differenceMap_eq_zero
    (i : Fin m) (hd : 0 < d i) (I : Box (Fin (d i))) (N : ℕ)
    (K L : Box (Fin (d i))) (hK : K ∈ descendants I N) (hL : L ∈ descendants I N)
    (hnot : ¬ K < L) : averageMap i K * differenceMap i L = 0 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  obtain ⟨C, _, hb⟩ := f.2.2
  have ht := coordinateAverage_difference_eq_zero i hd I N K L hK hL hnot f.1
    (integrable_coordinateSlice f.1 f.2.1 C hb i I)
  simpa only [Module.End.mul_apply, averageMap_apply, differenceMap_apply,
    LinearMap.zero_apply, ZeroMemClass.coe_zero] using ht

/-- Only the selected coordinate needs a dyadic relation for this vanishing. -/
theorem averageMap_mul_productDifferenceMap_eq_zero
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (B : Finset (Fin m)) (i : Fin m) (hi : i ∈ B) (hd : 0 < d i)
    (K : Box (Fin (d i))) (L : ∀ i, Box (Fin (d i)))
    (hK : K ∈ descendants (I i) (N i)) (hL : L i ∈ descendants (I i) (N i))
    (hnot : ¬ K < L i) : averageMap i K * productDifferenceMap B L = 0 := by
  rw [productDifferenceMap_eq_mul_erase B i hi L, ← mul_assoc,
    averageMap_mul_differenceMap_eq_zero i hd (I i) (N i) K (L i) hK hL hnot,
    zero_mul]

/-- Extract an average on the right using the proved average commutation. -/
theorem productAverageMap_eq_erase_mul (A : Finset (Fin m)) (i : Fin m)
    (hi : i ∈ A) (K : ∀ i, Box (Fin (d i))) :
    productAverageMap A K = productAverageMap (A.erase i) K * averageMap i (K i) := by
  exact (Finset.noncommProd_erase_mul A hi (fun j => averageMap j (K j))
    (fun j _ k _ hjk => averageMap_commute j k hjk (K j) (K k))).symm

/-- The product cancellation used to preserve averages and obtain the representation:
failure of strict containment in one coordinate suffices. Only that coordinate
requires positive dimension. An empty average product remains the identity and
cannot satisfy this failure condition. Differences at the smallest retained scale
still use their children.

-/
theorem productAverageMap_mul_full_difference_eq_zero
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (A : Finset (Fin m))
    (K L : ∀ i, Box (Fin (d i)))
    (hK : ∀ i ∈ A, K i ∈ descendants (I i) (N i))
    (hL : ∀ i, L i ∈ descendants (I i) (N i))
    (hbad : ∃ i ∈ A, 0 < d i ∧ ¬ K i < L i) :
    productAverageMap A K * productDifferenceMap Finset.univ L = 0 := by
  obtain ⟨i, hi, hd, hnot⟩ := hbad
  rw [productAverageMap_eq_erase_mul A i hi K, mul_assoc,
    averageMap_mul_productDifferenceMap_eq_zero I N Finset.univ i (Finset.mem_univ i)
      hd (K i) L (hK i hi) (hL i) hnot,
    mul_zero]

end ReyZygmund.Geometry
