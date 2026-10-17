import ReyZygmund.Geometry.ProductMaps
import ReyZygmund.Geometry.ComposedDifferenceSteps

/-!
# Partial coordinate operators on bounded measurable functions

The partial operators compose their factors in increasing coordinate order. On
bounded measurable functions, these compositions equal products of commuting
linear coordinate operators.
-/

open BoxIntegral
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- The partial average may be indexed by the sorted coordinate set. -/
theorem partialAverage_eq_foldr (A : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) (f : ProductPoint d → ℝ) :
    MathlibOnly.partialAverage A (fun i => Q i) f =
      (A.sort (· ≤ ·)).foldr (fun i g => coordinateAverage i (Q i) g) f := by
  let e : A ↪ Fin m := ⟨Subtype.val, Subtype.val_injective⟩
  have he : (Finset.univ : Finset A).map e = A := by
    ext i
    simp [e]
  have hs := Finset.map_sort e (Finset.univ : Finset A) (· ≤ ·) (· ≤ ·)
    (fun _ _ _ _ => Iff.rfl)
  rw [he] at hs
  rw [← hs, List.foldr_map]
  rfl

/-- On bounded measurable functions, the partial average is the product
of the commuting coordinate average maps. -/
theorem partialAverage_eq_productAverageMap (A : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) (f : boundedMeasurableFunctions d) :
    MathlibOnly.partialAverage A (fun i => Q i) f.1 =
      (productAverageMap A Q f).1 := by
  rw [partialAverage_eq_foldr]
  have hprod : productAverageMap A Q =
      ((A.sort (· ≤ ·)).map (fun i => averageMap i (Q i))).prod := by
    simpa only [productAverageMap, Finset.sort_toFinset] using
      (Finset.noncommProd_toFinset (A.sort (· ≤ ·))
        (fun i => averageMap i (Q i))
        (fun i _ j _ hij => averageMap_commute i j hij (Q i) (Q j))
        (A.sort_nodup (· ≤ ·)))
  rw [hprod]
  generalize A.sort (· ≤ ·) = L
  induction L with
  | nil => rfl
  | cons i L ih =>
    simpa only [List.foldr_cons, List.map_cons, List.prod_cons,
      Module.End.mul_apply, averageMap_apply] using
      congrArg (coordinateAverage i (Q i)) ih

/-- On bounded measurable functions, the partial difference is the
product of the commuting coordinate difference maps. -/
theorem partialDifference_eq_productDifferenceMap (A : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) (f : boundedMeasurableFunctions d) :
    MathlibOnly.partialDifference A (fun i => Q i) f.1 =
      (productDifferenceMap A Q f).1 := by
  rw [partialDifference_eq_foldr]
  have hprod : productDifferenceMap A Q =
      ((A.sort (· ≤ ·)).map (fun i => differenceMap i (Q i))).prod := by
    simpa only [productDifferenceMap, Finset.sort_toFinset] using
      (Finset.noncommProd_toFinset (A.sort (· ≤ ·))
        (fun i => differenceMap i (Q i))
        (fun i _ j _ hij => differenceMap_commute i j hij (Q i) (Q j))
        (A.sort_nodup (· ≤ ·)))
  rw [hprod]
  generalize A.sort (· ≤ ·) = L
  induction L with
  | nil => rfl
  | cons i L ih =>
    simpa only [List.foldr_cons, List.map_cons, List.prod_cons,
      Module.End.mul_apply, differenceMap_apply] using
      congrArg (coordinateDifference i (Q i)) ih

/-- The full difference is the product over all coordinate maps. -/
theorem fullDifference_eq_productDifferenceMap
    (Q : ∀ i, Box (Fin (d i))) (f : boundedMeasurableFunctions d) :
    MathlibOnly.fullDifference Q f.1 =
      (productDifferenceMap Finset.univ Q f).1 :=
  partialDifference_eq_productDifferenceMap Finset.univ Q f

end ReyZygmund.Geometry
