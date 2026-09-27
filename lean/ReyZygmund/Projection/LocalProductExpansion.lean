import ReyZygmund.Projection.LocalCancellation
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! # The local product expansion

The indices vary only in the selected coordinates. Fixing every other coordinate
at its top cube avoids multiplicity and includes the case of zero depth in an
unused coordinate.

-/

noncomputable section

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Projection

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private def localIndices (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (R : ∀ i, Box (Fin (d i))) (A : Finset (Fin m)) :
    Finset (∀ i, Box (Fin (d i))) :=
  Fintype.piFinset (fun i => if i ∈ A then
    (interior (I i) (N i)).filter (fun Q => Q ≤ R i) else {I i})

private theorem localIndices_empty (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (R : ∀ i, Box (Fin (d i))) : localIndices I N R ∅ = {I} := by
  simp [localIndices, Fintype.piFinset_singleton]

private theorem localIndices_univ (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (R : ∀ i, Box (Fin (d i))) :
    localIndices I N R Finset.univ =
      (productInterior I N).filter (fun L => ∀ i, L i ≤ R i) := by
  ext L
  simp only [localIndices, Fintype.mem_piFinset, Finset.mem_univ, ite_true,
    Finset.mem_filter, mem_productInterior]
  exact forall_and

private theorem localIndices_fixed (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (R : ∀ i, Box (Fin (d i))) (A : Finset (Fin m))
    {L : ∀ i, Box (Fin (d i))} (hL : L ∈ localIndices I N R A)
    {j : Fin m} (hj : j ∉ A) : L j = I j := by
  have h := Fintype.mem_piFinset.mp hL j
  simpa only [hj, ite_false, Finset.mem_singleton] using h

private theorem sum_localIndices_insert {V : Type*} [AddCommMonoid V]
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (R : ∀ i, Box (Fin (d i))) (A : Finset (Fin m))
    (j : Fin m) (hj : j ∉ A) (H : (∀ i, Box (Fin (d i))) → V) :
    (∑ L ∈ localIndices I N R (insert j A), H L) =
      ∑ Q ∈ (interior (I j) (N j)).filter (fun Q => Q ≤ R j),
        ∑ K ∈ localIndices I N R A, H (Function.update K j Q) := by
  symm
  rw [← Finset.sum_product
    ((interior (I j) (N j)).filter (fun Q => Q ≤ R j)) (localIndices I N R A)
    (fun pair => H (Function.update pair.2 j pair.1))]
  apply Finset.sum_bij (fun pair _ => Function.update pair.2 j pair.1)
  · intro pair hpair
    obtain ⟨hQ, hK⟩ := Finset.mem_product.mp hpair
    apply Fintype.mem_piFinset.mpr
    intro i
    by_cases hij : i = j
    · subst i
      simpa only [Finset.mem_insert_self, ite_true, Function.update_self] using hQ
    · have hKi := Fintype.mem_piFinset.mp hK i
      simpa only [Finset.mem_insert, hij, false_or, Function.update_of_ne hij] using hKi
  · intro a ha b hb heq
    have hQ : a.1 = b.1 := by simpa using congrFun heq j
    have hK : a.2 = b.2 := by
      funext i
      by_cases hij : i = j
      · subst i
        rw [localIndices_fixed I N R A (Finset.mem_product.mp ha).2 hj,
          localIndices_fixed I N R A (Finset.mem_product.mp hb).2 hj]
      · simpa only [Function.update_of_ne hij] using congrFun heq i
    exact Prod.ext hQ hK
  · intro L hL
    have hQ : L j ∈ (interior (I j) (N j)).filter (fun Q => Q ≤ R j) := by
      simpa only [Finset.mem_insert_self, ite_true] using Fintype.mem_piFinset.mp hL j
    have hK : Function.update L j (I j) ∈ localIndices I N R A := by
      apply Fintype.mem_piFinset.mpr
      intro i
      by_cases hij : i = j
      · subst i
        simp only [hj, ite_false, Function.update_self, Finset.mem_singleton]
      · have hLi := Fintype.mem_piFinset.mp hL i
        simpa only [Finset.mem_insert, hij, false_or, Function.update_of_ne hij] using hLi
    exact ⟨(L j, Function.update L j (I j)), Finset.mem_product.mpr ⟨hQ, hK⟩, by simp⟩
  · intro _ _
    rfl

private def localDifferenceSum (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (R : ∀ i, Box (Fin (d i))) (A : Finset (Fin m)) :
    Module.End ℝ (boundedMeasurableFunctions d) :=
  ∑ L ∈ localIndices I N R A, productDifferenceMap A L

private theorem localDifferenceSum_apply
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (R : ∀ i, Box (Fin (d i))) (A : Finset (Fin m))
    (F : boundedMeasurableFunctions d) :
    (localDifferenceSum I N R A F).1 =
      ∑ L ∈ localIndices I N R A, (productDifferenceMap A L F).1 := by
  funext x
  simp [localDifferenceSum, Finset.sum_apply]

private theorem localDifferenceSum_empty
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (R : ∀ i, Box (Fin (d i))) : localDifferenceSum I N R ∅ = 1 := by
  simp [localDifferenceSum, localIndices_empty]

private theorem localDifferenceSum_insert
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (R : ∀ i, Box (Fin (d i))) (A : Finset (Fin m))
    (j : Fin m) (hj : j ∉ A) :
    localDifferenceSum I N R (insert j A) =
      (∑ Q ∈ (interior (I j) (N j)).filter (fun Q => Q ≤ R j), differenceMap j Q) *
        localDifferenceSum I N R A := by
  unfold localDifferenceSum
  rw [sum_localIndices_insert I N R A j hj, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro Q _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K _
  rw [productDifferenceMap_insert A j hj, Function.update_self]
  congr 1
  apply productDifferenceMap_congr
  intro i hi
  exact Function.update_of_ne (ne_of_mem_of_not_mem hi hj) Q K

private theorem localDifferenceSum_closure
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (R : ∀ i, Box (Fin (d i))) (A : Finset (Fin m))
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) :
    ProductLeafConstant I N (localDifferenceSum I N R A F).1 ∧
      ∀ x, x ∉ productBox I → (localDifferenceSum I N R A F).1 x = 0 := by
  have hterm : ∀ L ∈ localIndices I N R A,
      ProductLeafConstant I N (productDifferenceMap A L F).1 ∧
        ∀ x, x ∉ productBox I → (productDifferenceMap A L F).1 x = 0 := by
    intro L hL
    apply productDifferenceMap_productStep_closure I N F hf hs A L
    intro i hi
    have hLi := Fintype.mem_piFinset.mp hL i
    exact (Finset.mem_filter.mp (by simpa only [hi, ite_true] using hLi)).1
  rw [localDifferenceSum_apply]
  refine ⟨productLeafConstant_finsetSum _ _ (fun L hL => (hterm L hL).1), ?_⟩
  intro x hx
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero (fun L hL => (hterm L hL).2 x hx)

private theorem coordinate_local_telescope
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (j : Fin m) (hd : 0 < d j) (R : Box (Fin (d j)))
    (hR : R ∈ descendants (I j) (N j)) (F : boundedMeasurableFunctions d)
    (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (x : ProductPoint d) (hx : x j ∈ R) :
    ((∑ Q ∈ (interior (I j) (N j)).filter (fun Q => Q ≤ R), differenceMap j Q) F).1 x =
      F.1 x - (averageMap j R F).1 x := by
  have hind : (productBox I).indicator F.1 = F.1 := by
    funext y
    by_cases hy : y ∈ productBox I
    · exact Set.indicator_of_mem hy F.1
    · simp [hy, hs y hy]
  have hleaf := productStep_coordinate_leafConstant I N F.1 hf j x
  rw [hind] at hleaf
  have ht := one_coordinate_telescope (d j) hd (I j) (N j) R hR
    (fun y => F.1 (Function.update x j y)) hleaf
  have hv := congrFun (ht.1.trans ht.2) (x j)
  simpa [LinearMap.sum_apply, Finset.sum_apply, differenceMap_apply,
    coordinateDifference_slice, averageMap_apply, coordinateAverage, hx] using hv

private def signedAverageSum (R : ∀ i, Box (Fin (d i))) (A : Finset (Fin m)) :
    Module.End ℝ (boundedMeasurableFunctions d) :=
  ∑ B ∈ A.powerset, (-1 : ℝ) ^ B.card • productAverageMap B R

private theorem signedAverageSum_insert
    (R : ∀ i, Box (Fin (d i))) (A : Finset (Fin m))
    (j : Fin m) (hj : j ∉ A) :
    signedAverageSum R (insert j A) =
      signedAverageSum R A - averageMap j (R j) * signedAverageSum R A := by
  unfold signedAverageSum
  rw [Finset.sum_powerset_insert hj]
  have hterm : ∀ B ∈ A.powerset,
      (-1 : ℝ) ^ (insert j B).card • productAverageMap (insert j B) R =
        -(averageMap j (R j) * ((-1 : ℝ) ^ B.card • productAverageMap B R)) := by
    intro B hB
    have hjB : j ∉ B := fun h => hj ((Finset.mem_powerset.mp hB) h)
    rw [Finset.card_insert_of_notMem hjB, pow_succ, mul_neg_one,
      productAverageMap_insert B j hjB]
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    funext x
    simp [Module.End.mul_apply]
  simp_rw [Finset.sum_congr rfl hterm]
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  simp [Module.End.mul_apply, Finset.sum_apply, map_sum, sub_eq_add_neg]

private theorem average_congr_on_rectangle
    (R : ∀ i, Box (Fin (d i))) (F G : boundedMeasurableFunctions d)
    (hFG : ∀ y ∈ productBox R, F.1 y = G.1 y)
    (j : Fin m) (x : ProductPoint d) (hx : x ∈ productBox R) :
    (averageMap j (R j) F).1 x = (averageMap j (R j) G).1 x := by
  simp only [averageMap_apply, coordinateAverage_of_mem j (R j) _ x
    ((mem_productBox R x).mp hx j)]
  congr 1
  apply setIntegral_congr_fun (R j).measurableSet_coe
  intro y hy
  apply hFG
  apply (mem_productBox R _).mpr
  intro i
  by_cases hij : i = j
  · subst i
    simpa using hy
  · simpa [hij] using (mem_productBox R x).mp hx i

private theorem localDifferenceSum_eq_signedAverageSum_on_rectangle
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (R : ∀ i, Box (Fin (d i))) (hR : ∀ i, R i ∈ descendants (I i) (N i))
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) (A : Finset (Fin m)) :
    ∀ x ∈ productBox R,
      (localDifferenceSum I N R A F).1 x = (signedAverageSum R A F).1 x := by
  induction A using Finset.induction_on with
  | empty =>
    intro x _
    simp [localDifferenceSum_empty, signedAverageSum]
  | @insert j A hj ih =>
    intro x hx
    have hc := localDifferenceSum_closure I N R A F hf hs
    have ht := coordinate_local_telescope I N j (hd j) (R j) (hR j)
      (localDifferenceSum I N R A F) hc.1 hc.2 x ((mem_productBox R x).mp hx j)
    rw [localDifferenceSum_insert I N R A j hj, Module.End.mul_apply, ht]
    rw [signedAverageSum_insert R A j hj]
    change _ = (signedAverageSum R A F).1 x -
      (averageMap j (R j) (signedAverageSum R A F)).1 x
    rw [ih x hx, average_congr_on_rectangle R _ _ ih j x hx]

/-- The local product telescope and its signed expansion, with equality on `R`.
-/
theorem local_product_expansion
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (R : ∀ i, Box (Fin (d i))) (hR : ∀ i, R i ∈ descendants (I i) (N i))
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (x : ProductPoint d) (hx : x ∈ productBox R) :
    (∑ L ∈ (productInterior I N).filter (fun L => ∀ i, L i ≤ R i),
      (productDifferenceMap Finset.univ L F).1 x) =
      ∑ B ∈ (Finset.univ : Finset (Fin m)).powerset,
        (-1 : ℝ) ^ B.card * (productAverageMap B R F).1 x := by
  have h := localDifferenceSum_eq_signedAverageSum_on_rectangle I N hd R hR F hf hs
    Finset.univ x hx
  simpa [localDifferenceSum_apply, localIndices_univ, signedAverageSum,
    Finset.sum_apply] using h

end ReyZygmund.Projection
