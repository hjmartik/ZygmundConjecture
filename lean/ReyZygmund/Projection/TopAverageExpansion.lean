import ReyZygmund.Geometry.PartialIndices
import ReyZygmund.Projection.Properties
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! # Partial telescopes and top-cube averages

Only selected coordinates vary in the difference sum; the others stay at the top
cubes. Preservation of top-cube averages then replaces each nonempty averaged term
of the projection by the corresponding average of the original signed input.


-/

noncomputable section

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Projection

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private def partialDifferenceSum (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A : Finset (Fin m)) : Module.End ℝ (boundedMeasurableFunctions d) :=
  ∑ L ∈ partialInterior I N A, productDifferenceMap A L

private theorem partialDifferenceSum_apply
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (A : Finset (Fin m))
    (F : boundedMeasurableFunctions d) :
    (partialDifferenceSum I N A F).1 =
      ∑ L ∈ partialInterior I N A, (productDifferenceMap A L F).1 := by
  funext x
  simp [partialDifferenceSum, Finset.sum_apply]

private theorem partialDifferenceSum_empty
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) :
    partialDifferenceSum I N ∅ = 1 := by
  simp [partialDifferenceSum]

private theorem partialDifferenceSum_insert
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (A : Finset (Fin m))
    (j : Fin m) (hj : j ∉ A) :
    partialDifferenceSum I N (insert j A) =
      (∑ Q ∈ interior (I j) (N j), differenceMap j Q) * partialDifferenceSum I N A := by
  unfold partialDifferenceSum
  rw [sum_partialInterior_insert I N A j hj, Finset.sum_mul]
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

private theorem partialDifferenceSum_closure
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (A : Finset (Fin m))
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) :
    ProductLeafConstant I N (partialDifferenceSum I N A F).1 ∧
      ∀ x, x ∉ productBox I → (partialDifferenceSum I N A F).1 x = 0 := by
  have hterm : ∀ L ∈ partialInterior I N A,
      ProductLeafConstant I N (productDifferenceMap A L F).1 ∧
        ∀ x, x ∉ productBox I → (productDifferenceMap A L F).1 x = 0 := by
    intro L hL
    exact productDifferenceMap_productStep_closure I N F hf hs A L
      (fun i hi => partialInterior_mem_selected hL hi)
  rw [partialDifferenceSum_apply]
  refine ⟨productLeafConstant_finsetSum _ _ (fun L hL => (hterm L hL).1), ?_⟩
  intro x hx
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero (fun L hL => (hterm L hL).2 x hx)

private theorem coordinate_root_telescope
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (j : Fin m) (hd : 0 < d j) (F : boundedMeasurableFunctions d)
    (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (x : ProductPoint d) (hx : x j ∈ I j) :
    ((∑ Q ∈ interior (I j) (N j), differenceMap j Q) F).1 x =
      F.1 x - (averageMap j (I j) F).1 x := by
  have hind : (productBox I).indicator F.1 = F.1 := by
    funext y
    by_cases hy : y ∈ productBox I
    · exact Set.indicator_of_mem hy F.1
    · simp [hy, hs y hy]
  have hleaf := productStep_coordinate_leafConstant I N F.1 hf j x
  rw [hind] at hleaf
  have hroot : I j ∈ descendants (I j) (N j) :=
    mem_descendants.mpr ⟨0, Nat.zero_le _, Prepartition.mem_top.mpr rfl⟩
  have hfilter : (interior (I j) (N j)).filter (fun Q => Q ≤ I j) =
      interior (I j) (N j) := by
    apply Finset.filter_eq_self.mpr
    intro Q hQ
    exact le_of_mem_descendants (interior_subset_descendants (I j) (N j) hQ)
  have ht := one_coordinate_telescope (d j) hd (I j) (N j) (I j) hroot
    (fun y => F.1 (Function.update x j y)) hleaf
  have hv := congrFun (ht.1.trans ht.2) (x j)
  rw [hfilter] at hv
  simpa [LinearMap.sum_apply, Finset.sum_apply, differenceMap_apply,
    coordinateDifference_slice, averageMap_apply, coordinateAverage, hx] using hv

private def rootSignedAverageSum (I : ∀ i, Box (Fin (d i))) (A : Finset (Fin m)) :
    Module.End ℝ (boundedMeasurableFunctions d) :=
  ∑ B ∈ A.powerset, (-1 : ℝ) ^ B.card • productAverageMap B I

private theorem rootSignedAverageSum_insert
    (I : ∀ i, Box (Fin (d i))) (A : Finset (Fin m)) (j : Fin m) (hj : j ∉ A) :
    rootSignedAverageSum I (insert j A) =
      rootSignedAverageSum I A - averageMap j (I j) * rootSignedAverageSum I A := by
  unfold rootSignedAverageSum
  rw [Finset.sum_powerset_insert hj]
  have hterm : ∀ B ∈ A.powerset,
      (-1 : ℝ) ^ (insert j B).card • productAverageMap (insert j B) I =
        -(averageMap j (I j) * ((-1 : ℝ) ^ B.card • productAverageMap B I)) := by
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

private theorem root_average_congr
    (I : ∀ i, Box (Fin (d i))) (F G : boundedMeasurableFunctions d)
    (hFG : ∀ y ∈ productBox I, F.1 y = G.1 y)
    (j : Fin m) (x : ProductPoint d) (hx : x ∈ productBox I) :
    (averageMap j (I j) F).1 x = (averageMap j (I j) G).1 x := by
  simp only [averageMap_apply, coordinateAverage_of_mem j (I j) _ x
    ((mem_productBox I x).mp hx j)]
  congr 1
  apply setIntegral_congr_fun (I j).measurableSet_coe
  intro y hy
  apply hFG
  apply (mem_productBox I _).mpr
  intro i
  by_cases hij : i = j
  · subst i
    simpa using hy
  · simpa [hij] using (mem_productBox I x).mp hx i

private theorem partialDifferenceSum_eq_rootSignedAverageSum
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) (A : Finset (Fin m)) :
    ∀ x ∈ productBox I,
      (partialDifferenceSum I N A F).1 x = (rootSignedAverageSum I A F).1 x := by
  induction A using Finset.induction_on with
  | empty =>
    intro x _
    simp [partialDifferenceSum_empty, rootSignedAverageSum]
  | @insert j A hj ih =>
    intro x hx
    have hc := partialDifferenceSum_closure I N A F hf hs
    have ht := coordinate_root_telescope I N j (hd j)
      (partialDifferenceSum I N A F) hc.1 hc.2 x ((mem_productBox I x).mp hx j)
    rw [partialDifferenceSum_insert I N A j hj, Module.End.mul_apply, ht]
    rw [rootSignedAverageSum_insert I A j hj]
    change _ = (rootSignedAverageSum I A F).1 x -
      (averageMap j (I j) (rootSignedAverageSum I A F)).1 x
    rw [ih x hx, root_average_congr I _ _ ih j x hx]

/-- The partial interior sum telescopes to signed top-cube averages on the top
rectangle, including an empty selected set and zero coordinate depths. -/
theorem partial_telescope_eq_top_averages
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) (A : Finset (Fin m))
    (x : ProductPoint d) (hx : x ∈ productBox I) :
    (∑ L ∈ partialInterior I N A, (productDifferenceMap A L F).1 x) =
      ∑ B ∈ A.powerset, (-1 : ℝ) ^ B.card * (productAverageMap B I F).1 x := by
  have h := partialDifferenceSum_eq_rootSignedAverageSum I N hd F hf hs A x hx
  simpa [partialDifferenceSum_apply, rootSignedAverageSum, Finset.sum_apply] using h

private theorem productAverageMap_mul_finiteProjectionMap_of_nonempty
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (B : Finset (Fin m)) (hB : B.Nonempty) :
    productAverageMap B I * finiteProjectionMap I N G = productAverageMap B I := by
  obtain ⟨i, hi⟩ := hB
  rw [productAverageMap_eq_erase_mul B i hi I, mul_assoc,
    averageMap_mul_finiteProjectionMap I N G i (hd i)]

/-- The top-average decomposition for any selected coordinates. Every nonempty
averaged term is an average of the original input. -/
theorem finiteProjection_top_average_decomposition
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (f : boundedMeasurableFunctions d)
    (hf : ProductLeafConstant I N f.1)
    (hs : ∀ x, x ∉ productBox I → f.1 x = 0) (A : Finset (Fin m))
    (x : ProductPoint d) (hx : x ∈ productBox I) :
    (∑ L ∈ partialInterior I N A,
      (productDifferenceMap A L (finiteProjectionMap I N G f)).1 x) =
      (finiteProjectionMap I N G f).1 x +
        ∑ B ∈ A.powerset.erase ∅,
          (-1 : ℝ) ^ B.card * (productAverageMap B I f).1 x := by
  have hc := finiteProjectionMap_productStep_closure I N G f hf hs
  rw [partial_telescope_eq_top_averages I N hd _ hc.1 hc.2 A x hx]
  rw [← Finset.add_sum_erase A.powerset
    (fun B => (-1 : ℝ) ^ B.card *
      (productAverageMap B I (finiteProjectionMap I N G f)).1 x)
    (Finset.mem_powerset.mpr (Finset.empty_subset A))]
  simp only [Finset.card_empty, pow_zero, productAverageMap_empty,
    Module.End.one_apply, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro B hB
  have hne : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hB).1
  have hmap := productAverageMap_mul_finiteProjectionMap_of_nonempty I N hd G B hne
  have hval := congrArg
    (fun T : Module.End ℝ (boundedMeasurableFunctions d) => (T f).1 x) hmap
  rw [show (productAverageMap B I (finiteProjectionMap I N G f)).1 x =
      (productAverageMap B I f).1 x by
    simpa only [Module.End.mul_apply] using hval]

end ReyZygmund.Projection
