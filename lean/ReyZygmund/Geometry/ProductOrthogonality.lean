import ReyZygmund.Geometry.ProductMaps
import ReyZygmund.Geometry.FiniteDifferenceAlgebra

/-!
# Difference orthogonality on the product space

The one-coordinate identities are lifted through coordinate slices.
Finite products then select exactly the matching coordinate indices. These
identities apply to the concrete bounded measurable functions; no operator
algebra is assumed as part of their definition.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

theorem coordinateDifference_same
    (i : Fin m) (hd : 0 < d i) (I : Box (Fin (d i))) (N : ℕ)
    (L Q : Box (Fin (d i))) (hL : L ∈ descendants I N) (hQ : Q ∈ descendants I N)
    (f : ProductPoint d → ℝ)
    (hf : ∀ x, IntegrableOn (fun y => f (Function.update x i y))
      (I : Set (Fin (d i) → ℝ)) volume) :
    coordinateDifference i L (coordinateDifference i Q f) =
      if L = Q then coordinateDifference i Q f else 0 := by
  funext x
  have hs : (fun y => coordinateDifference i Q f (Function.update x i y)) =
      boxDifference Q (fun y => f (Function.update x i y)) := by
    funext y
    simp [coordinateDifference_slice]
  rw [coordinateDifference_slice, hs]
  have ht := congrFun (finite_difference_difference (d i) hd I N L Q hL hQ
    (fun y => f (Function.update x i y)) (hf x)) (x i)
  by_cases h : L = Q <;> simpa [h, coordinateDifference_slice] using ht

theorem differenceMap_mul_same
    (i : Fin m) (hd : 0 < d i) (I : Box (Fin (d i))) (N : ℕ)
    (L Q : Box (Fin (d i))) (hL : L ∈ descendants I N) (hQ : Q ∈ descendants I N) :
    differenceMap i L * differenceMap i Q =
      if L = Q then differenceMap i Q else 0 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  obtain ⟨C, _, hb⟩ := f.2.2
  have ht := coordinateDifference_same i hd I N L Q hL hQ f.1
    (integrable_coordinateSlice f.1 f.2.1 C hb i I)
  by_cases h : L = Q <;>
    simpa only [Module.End.mul_apply, differenceMap_apply, h, ite_true, ite_false,
      LinearMap.zero_apply, ZeroMemClass.coe_zero] using ht

/-- Extract one coordinate factor, with the remaining order justified by the
already proved distinct-coordinate commutation. -/
theorem productDifferenceMap_eq_mul_erase (B : Finset (Fin m)) (i : Fin m)
    (hi : i ∈ B) (L : ∀ i, Box (Fin (d i))) :
    productDifferenceMap B L =
      differenceMap i (L i) * productDifferenceMap (B.erase i) L := by
  conv_lhs => rw [← Finset.insert_erase hi]
  exact productDifferenceMap_insert (B.erase i) i (by simp) L

theorem differenceMap_mul_productDifferenceMap
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (B : Finset (Fin m)) (i : Fin m) (hi : i ∈ B) (hd : 0 < d i)
    (Q : Box (Fin (d i))) (L : ∀ i, Box (Fin (d i)))
    (hQ : Q ∈ descendants (I i) (N i)) (hL : L i ∈ descendants (I i) (N i)) :
    differenceMap i Q * productDifferenceMap B L =
      if Q = L i then productDifferenceMap B L else 0 := by
  rw [productDifferenceMap_eq_mul_erase B i hi L, ← mul_assoc,
    differenceMap_mul_same i hd (I i) (N i) Q (L i) hQ hL]
  by_cases h : Q = L i <;> simp [h]

/-- Product orthogonality selects exactly the matching indices in the cross-coordinate
calculation. -/
theorem productDifferenceMap_mul_full
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (hd : ∀ i, 0 < d i) (A : Finset (Fin m))
    (K L : ∀ i, Box (Fin (d i)))
    (hK : ∀ i ∈ A, K i ∈ descendants (I i) (N i))
    (hL : ∀ i, L i ∈ descendants (I i) (N i)) :
    productDifferenceMap A K * productDifferenceMap Finset.univ L =
      if ∀ i ∈ A, K i = L i then productDifferenceMap Finset.univ L else 0 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
    rw [productDifferenceMap_insert A i hi K, mul_assoc,
      ih (fun j hj => hK j (Finset.mem_insert_of_mem hj))]
    by_cases hmatch : ∀ j ∈ A, K j = L j
    · rw [ite_eq_left hmatch,
        differenceMap_mul_productDifferenceMap I N Finset.univ i (Finset.mem_univ i)
          (hd i) (K i) L (hK i (Finset.mem_insert_self i A)) (hL i)]
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

theorem productDifferenceMap_congr (A : Finset (Fin m))
    (K L : ∀ i, Box (Fin (d i))) (h : ∀ i ∈ A, K i = L i) :
    productDifferenceMap A K = productDifferenceMap A L := by
  apply Finset.noncommProd_congr rfl
  intro i hi
  rw [h i hi]

/-- The surviving full difference factors into the remaining coordinate and
the prescribed other-coordinate difference. -/
theorem productDifferenceMap_full_of_matches
    (j : Fin m) (K L : ∀ i, Box (Fin (d i)))
    (h : ∀ i, i ≠ j → L i = K i) :
    productDifferenceMap Finset.univ L =
      differenceMap j (L j) * productDifferenceMap (Finset.univ.erase j) K := by
  rw [productDifferenceMap_eq_mul_erase Finset.univ j (Finset.mem_univ j) L]
  congr 1
  apply productDifferenceMap_congr
  intro i hi
  exact h i (Finset.mem_erase.mp hi).1

theorem productDifferenceMap_mul_full_erase
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (hd : ∀ i, 0 < d i) (j : Fin m) (K L : ∀ i, Box (Fin (d i)))
    (hK : ∀ i, i ≠ j → K i ∈ descendants (I i) (N i))
    (hL : ∀ i, L i ∈ descendants (I i) (N i)) :
    productDifferenceMap (Finset.univ.erase j) K * productDifferenceMap Finset.univ L =
      if ∀ i, i ≠ j → L i = K i then
        differenceMap j (L j) * productDifferenceMap (Finset.univ.erase j) K else 0 := by
  rw [productDifferenceMap_mul_full I N hd _ K L
    (fun i hi => hK i (Finset.mem_erase.mp hi).1) hL]
  have hc : (∀ i ∈ Finset.univ.erase j, K i = L i) ↔ (∀ i, i ≠ j → L i = K i) := by
    constructor
    · intro h i hij
      exact (h i (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)).symm
    · intro h i hi
      exact (h i (Finset.mem_erase.mp hi).1).symm
  by_cases h : ∀ i, i ≠ j → L i = K i
  · rw [ite_eq_left (hc.mpr h), ite_eq_left h, productDifferenceMap_full_of_matches j K L h]
  · rw [ite_eq_right (fun hh => h (hc.mp hh)), ite_eq_right h]

end ReyZygmund.Geometry
