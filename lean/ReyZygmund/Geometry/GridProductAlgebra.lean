import ReyZygmund.Geometry.GridDifferenceAlgebra
import ReyZygmund.Geometry.AverageDifferenceMaps
import ReyZygmund.Geometry.RawDifferenceBridge

/-! # Product difference algebra on the full grids

The one-coordinate identities apply at arbitrary integer generations to integrable
slices of bounded measurable functions. The rectangle-integral formula is proved
on the same function class, so all its averages are defined by integrable
functions. A common top rectangle or smallest scale is not required.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem grid_coordinateDifference_same
    (i : Fin m) (hd : 0 < d i) (D : DyadicGrid (d i))
    {a b : ℤ} (L Q : Box (Fin (d i)))
    (hL : L ∈ D.cubes a) (hQ : Q ∈ D.cubes b)
    (f : ProductPoint d → ℝ)
    (hf : ∀ x, IntegrableOn (fun y => f (Function.update x i y))
      (Q : Set (Fin (d i) → ℝ)) volume) :
    coordinateDifference i L (coordinateDifference i Q f) =
      if L = Q then coordinateDifference i Q f else 0 := by
  funext x
  have hs : (fun y => coordinateDifference i Q f (Function.update x i y)) =
      boxDifference Q (fun y => f (Function.update x i y)) := by
    funext y
    simp [coordinateDifference_slice]
  rw [coordinateDifference_slice, hs]
  have ht := congrFun (grid_difference_difference hd D L Q hL hQ
    (fun y => f (Function.update x i y)) (hf x)) (x i)
  by_cases h : L = Q <;> simpa [h, coordinateDifference_slice] using ht

/-- Same-coordinate orthogonality for arbitrary signed grid generations. -/
theorem grid_differenceMap_mul_same
    (i : Fin m) (hd : 0 < d i) (D : DyadicGrid (d i))
    {a b : ℤ} (L Q : Box (Fin (d i)))
    (hL : L ∈ D.cubes a) (hQ : Q ∈ D.cubes b) :
    differenceMap i L * differenceMap i Q =
      if L = Q then differenceMap i Q else 0 := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  obtain ⟨C, _, hb⟩ := F.2.2
  have ht := grid_coordinateDifference_same i hd D L Q hL hQ F.1
    (integrable_coordinateSlice F.1 F.2.1 C hb i Q)
  by_cases h : L = Q <;>
    simpa only [Module.End.mul_apply, differenceMap_apply, h, ite_true, ite_false,
      LinearMap.zero_apply, ZeroMemClass.coe_zero] using ht

private theorem grid_differenceMap_mul_productDifferenceMap
    (B : Finset (Fin m)) (i : Fin m) (hi : i ∈ B) (hd : 0 < d i)
    (D : DyadicGrid (d i)) {a b : ℤ}
    (Q : Box (Fin (d i))) (L : ∀ i, Box (Fin (d i)))
    (hQ : Q ∈ D.cubes a) (hL : L i ∈ D.cubes b) :
    differenceMap i Q * productDifferenceMap B L =
      if Q = L i then productDifferenceMap B L else 0 := by
  rw [productDifferenceMap_eq_mul_erase B i hi L, ← mul_assoc,
    grid_differenceMap_mul_same i hd D Q (L i) hQ hL]
  by_cases h : Q = L i <;> simp [h]

/-- A selected product retains exactly its matching indices in the full
difference. The empty selected product is the identity. -/
theorem grid_productDifferenceMap_mul_full
    (D : ∀ i, DyadicGrid (d i)) (a b : Fin m → ℤ)
    (hd : ∀ i, 0 < d i) (A : Finset (Fin m))
    (K L : ∀ i, Box (Fin (d i)))
    (hK : ∀ i ∈ A, K i ∈ (D i).cubes (a i))
    (hL : ∀ i, L i ∈ (D i).cubes (b i)) :
    productDifferenceMap A K * productDifferenceMap Finset.univ L =
      if ∀ i ∈ A, K i = L i then productDifferenceMap Finset.univ L else 0 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
    rw [productDifferenceMap_insert A i hi K, mul_assoc,
      ih (fun j hj => hK j (Finset.mem_insert_of_mem hj))]
    by_cases hmatch : ∀ j ∈ A, K j = L j
    · rw [ite_eq_left hmatch,
        grid_differenceMap_mul_productDifferenceMap Finset.univ i (Finset.mem_univ i)
          (hd i) (D i) (K i) L (hK i (Finset.mem_insert_self i A)) (hL i)]
      have heq : (∀ j ∈ insert i A, K j = L j) ↔ K i = L i := by
        constructor
        · intro h
          exact h i (Finset.mem_insert_self i A)
        · intro h j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact h
          · exact hmatch j hj
      simp only [heq]
    · rw [ite_eq_right hmatch, mul_zero]
      have hn : ¬ ∀ j ∈ insert i A, K j = L j :=
        fun h => hmatch (fun j hj => h j (Finset.mem_insert_of_mem hj))
      rw [ite_eq_right hn]

private theorem grid_coordinateAverage_difference_eq_zero
    (i : Fin m) (hd : 0 < d i) (D : DyadicGrid (d i))
    {a b : ℤ} (K L : Box (Fin (d i)))
    (hK : K ∈ D.cubes a) (hL : L ∈ D.cubes b)
    (hnot : ¬ K < L) (f : ProductPoint d → ℝ)
    (hf : ∀ x, IntegrableOn (fun y => f (Function.update x i y))
      (L : Set (Fin (d i) → ℝ)) volume) :
    coordinateAverage i K (coordinateDifference i L f) = 0 := by
  funext x
  have hs : (fun y => coordinateDifference i L f (Function.update x i y)) =
      boxDifference L (fun y => f (Function.update x i y)) := by
    funext y
    simp [coordinateDifference_slice]
  change boxAverage K (fun y => coordinateDifference i L f (Function.update x i y))
    (x i) = 0
  rw [hs]
  have ht := congrFun (grid_average_difference hd D K L hK hL
    (fun y => f (Function.update x i y)) (hf x)) (x i)
  simpa [hnot] using ht

/-- The zero branch of the grid average–difference identity.
Equality, ancestors, and disjoint cubes all belong to this branch. -/
theorem grid_averageMap_mul_differenceMap_eq_zero
    (i : Fin m) (hd : 0 < d i) (D : DyadicGrid (d i))
    {a b : ℤ} (K L : Box (Fin (d i)))
    (hK : K ∈ D.cubes a) (hL : L ∈ D.cubes b)
    (hnot : ¬ K < L) : averageMap i K * differenceMap i L = 0 := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  obtain ⟨C, _, hb⟩ := F.2.2
  have ht := grid_coordinateAverage_difference_eq_zero i hd D K L hK hL hnot F.1
    (integrable_coordinateSlice F.1 F.2.1 C hb i L)
  simpa only [Module.End.mul_apply, averageMap_apply, differenceMap_apply,
    LinearMap.zero_apply, ZeroMemClass.coe_zero] using ht

/-- Only the extracted coordinate needs grid membership for this identity. -/
theorem grid_averageMap_mul_productDifferenceMap_eq_zero
    (B : Finset (Fin m)) (i : Fin m) (hi : i ∈ B) (hd : 0 < d i)
    (D : DyadicGrid (d i)) {a b : ℤ}
    (K : Box (Fin (d i))) (L : ∀ i, Box (Fin (d i)))
    (hK : K ∈ D.cubes a) (hL : L i ∈ D.cubes b)
    (hnot : ¬ K < L i) : averageMap i K * productDifferenceMap B L = 0 := by
  rw [productDifferenceMap_eq_mul_erase B i hi L, ← mul_assoc,
    grid_averageMap_mul_differenceMap_eq_zero i hd D K (L i) hK hL hnot, zero_mul]

/-- If strict containment fails in a selected coordinate, the average product
annihilates the full difference. This condition cannot occur for the empty set of
selected coordinates. -/
theorem grid_productAverageMap_mul_full_difference_eq_zero
    (D : ∀ i, DyadicGrid (d i)) (a b : Fin m → ℤ) (A : Finset (Fin m))
    (K L : ∀ i, Box (Fin (d i)))
    (hK : ∀ i ∈ A, K i ∈ (D i).cubes (a i))
    (hL : ∀ i, L i ∈ (D i).cubes (b i))
    (hbad : ∃ i ∈ A, 0 < d i ∧ ¬ K i < L i) :
    productAverageMap A K * productDifferenceMap Finset.univ L = 0 := by
  obtain ⟨i, hi, hd, hnot⟩ := hbad
  rw [productAverageMap_eq_erase_mul A i hi K, mul_assoc,
    grid_averageMap_mul_productDifferenceMap_eq_zero Finset.univ i (Finset.mem_univ i)
      hd (D i) (K i) L (hK i hi) (hL i) hnot, mul_zero]

/-- Orthogonality for the rectangle-integral expansion on bounded
measurable inputs. This does not assert cancellation for default integrals
of arbitrary nonintegrable functions. -/
theorem grid_rawProductDifference_same
    (D : ∀ i, DyadicGrid (d i)) (a b : Fin m → ℤ)
    (hd : ∀ i, 0 < d i) (L Q : ∀ i, Box (Fin (d i)))
    (hL : ∀ i, L i ∈ (D i).cubes (a i))
    (hQ : ∀ i, Q i ∈ (D i).cubes (b i))
    (F : boundedMeasurableFunctions d) :
    rawProductDifference L (rawProductDifference Q F.1) =
      if L = Q then rawProductDifference Q F.1 else 0 := by
  have hout : rawProductDifference L (rawProductDifference Q F.1) =
      (productDifferenceMap Finset.univ L (productDifferenceMap Finset.univ Q F)).1 := by
    rw [rawProductDifference_eq_productDifferenceMap Q F,
      rawProductDifference_eq_productDifferenceMap L (productDifferenceMap Finset.univ Q F)]
  rw [hout, rawProductDifference_eq_productDifferenceMap Q F]
  have hmatch : (∀ i ∈ (Finset.univ : Finset (Fin m)), L i = Q i) ↔ L = Q := by
    constructor
    · intro h
      exact funext (fun i => h i (Finset.mem_univ i))
    · rintro rfl
      exact fun _ _ => rfl
  have ht := congrArg (fun T : Module.End ℝ (boundedMeasurableFunctions d) => (T F).1)
    (grid_productDifferenceMap_mul_full D a b hd Finset.univ L Q
      (fun i _ => hL i) hQ)
  by_cases h : L = Q
  · rw [ite_eq_left (hmatch.mpr h)] at ht
    simpa only [h, ite_true, Module.End.mul_apply] using ht
  · have hn : ¬ ∀ i ∈ (Finset.univ : Finset (Fin m)), L i = Q i :=
      fun hp => h (hmatch.mp hp)
    rw [ite_eq_right hn] at ht
    simpa only [h, ite_false, Module.End.mul_apply,
      LinearMap.zero_apply, ZeroMemClass.coe_zero] using ht

end ReyZygmund.Geometry
