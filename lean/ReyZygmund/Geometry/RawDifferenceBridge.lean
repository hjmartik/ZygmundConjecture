import ReyZygmund.Geometry.GlobalDifferences
import ReyZygmund.Geometry.ProductMean
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! # Rectangle integrals and coordinate differences

The finite inclusion–exclusion formula equals the product of commuting coordinate
differences on bounded measurable inputs. Parent cubes in unselected coordinates
keep each tuple from being counted more than once. The final step uses the
integral formula for the product of coordinate averages.


-/

noncomputable section

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem differenceRectangles_mem_unselected
    {A : Finset (Fin m)} {Q R : ∀ i, Box (Fin (d i))}
    (hR : R ∈ differenceRectangles A Q) {j : Fin m} (hj : j ∉ A) :
    R j = Q j := by
  simpa only [hj, ite_false, Finset.mem_singleton] using Fintype.mem_piFinset.mp hR j

private theorem sum_differenceRectangles_insert {V : Type*} [AddCommMonoid V]
    (A : Finset (Fin m)) (j : Fin m) (hj : j ∉ A)
    (Q : ∀ i, Box (Fin (d i))) (H : (∀ i, Box (Fin (d i))) → V) :
    (∑ R ∈ differenceRectangles (insert j A) Q, H R) =
      ∑ P ∈ (Prepartition.splitCenter (Q j)).boxes,
        ∑ R ∈ differenceRectangles A Q, H (Function.update R j P) := by
  symm
  rw [← Finset.sum_product (Prepartition.splitCenter (Q j)).boxes
    (differenceRectangles A Q) (fun pair => H (Function.update pair.2 j pair.1))]
  apply Finset.sum_bij (fun pair _ => Function.update pair.2 j pair.1)
  · intro pair hpair
    obtain ⟨hP, hR⟩ := Finset.mem_product.mp hpair
    apply Fintype.mem_piFinset.mpr
    intro i
    by_cases hij : i = j
    · subst i
      simpa only [Finset.mem_insert_self, ite_true, Function.update_self] using hP
    · have hRi := Fintype.mem_piFinset.mp hR i
      simpa only [Finset.mem_insert, hij, false_or, Function.update_of_ne hij] using hRi
  · intro a ha b hb heq
    have hP : a.1 = b.1 := by simpa using congrFun heq j
    have hR : a.2 = b.2 := by
      funext i
      by_cases hij : i = j
      · subst i
        rw [differenceRectangles_mem_unselected (Finset.mem_product.mp ha).2 hj,
          differenceRectangles_mem_unselected (Finset.mem_product.mp hb).2 hj]
      · simpa only [Function.update_of_ne hij] using congrFun heq i
    exact Prod.ext hP hR
  · intro L hL
    have hP : L j ∈ (Prepartition.splitCenter (Q j)).boxes := by
      simpa only [Finset.mem_insert_self, ite_true] using Fintype.mem_piFinset.mp hL j
    have hR : Function.update L j (Q j) ∈ differenceRectangles A Q := by
      apply Fintype.mem_piFinset.mpr
      intro i
      by_cases hij : i = j
      · subst i
        simp only [hj, ite_false, Function.update_self, Finset.mem_singleton]
      · have hLi := Fintype.mem_piFinset.mp hL i
        simpa only [Finset.mem_insert, hij, false_or, Function.update_of_ne hij] using hLi
    exact ⟨(L j, Function.update L j (Q j)), Finset.mem_product.mpr ⟨hP, hR⟩, by simp⟩
  · intro _ _
    rfl

private theorem productAverageMap_update_unselected
    (S : Finset (Fin m)) (j : Fin m) (hj : j ∉ S)
    (R : ∀ i, Box (Fin (d i))) (P : Box (Fin (d j))) :
    productAverageMap S (Function.update R j P) = productAverageMap S R := by
  apply Finset.noncommProd_congr rfl
  intro i hi
  have hij : i ≠ j := by
    rintro rfl
    exact hj hi
  rw [Function.update_of_ne hij]

private def rectangleAverageSum (S A : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) : Module.End ℝ (boundedMeasurableFunctions d) :=
  ∑ R ∈ differenceRectangles A Q, productAverageMap S R

private theorem rectangleAverageSum_parent_insert
    (S A : Finset (Fin m)) (j : Fin m) (hjS : j ∉ S) (hjA : j ∉ A)
    (Q : ∀ i, Box (Fin (d i))) :
    rectangleAverageSum (insert j S) A Q =
      averageMap j (Q j) * rectangleAverageSum S A Q := by
  unfold rectangleAverageSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R hR
  rw [productAverageMap_insert S j hjS,
    differenceRectangles_mem_unselected hR hjA]

private theorem rectangleAverageSum_child_insert
    (S A : Finset (Fin m)) (j : Fin m) (hjS : j ∉ S) (hjA : j ∉ A)
    (Q : ∀ i, Box (Fin (d i))) :
    rectangleAverageSum (insert j S) (insert j A) Q =
      (∑ P ∈ (Prepartition.splitCenter (Q j)).boxes, averageMap j P) *
        rectangleAverageSum S A Q := by
  unfold rectangleAverageSum
  rw [sum_differenceRectangles_insert A j hjA Q, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro P _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R _
  rw [productAverageMap_insert S j hjS, Function.update_self,
    productAverageMap_update_unselected S j hjS]

private def differenceExpansion (S : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) : Module.End ℝ (boundedMeasurableFunctions d) :=
  ∑ A ∈ S.powerset, (-1 : ℝ) ^ (S.card - A.card) • rectangleAverageSum S A Q

private theorem differenceExpansion_insert
    (S : Finset (Fin m)) (j : Fin m) (hj : j ∉ S)
    (Q : ∀ i, Box (Fin (d i))) :
    differenceExpansion (insert j S) Q =
      differenceMap j (Q j) * differenceExpansion S Q := by
  unfold differenceExpansion
  rw [Finset.sum_powerset_insert hj, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  have hAS : A ⊆ S := Finset.mem_powerset.mp hA
  have hjA : j ∉ A := fun h => hj (hAS h)
  have hcard : A.card ≤ S.card := Finset.card_le_card hAS
  have hparent : (insert j S).card - A.card = S.card - A.card + 1 := by
    rw [Finset.card_insert_of_notMem hj]
    omega
  have hchild : (insert j S).card - (insert j A).card = S.card - A.card := by
    rw [Finset.card_insert_of_notMem hj, Finset.card_insert_of_notMem hjA]
    omega
  rw [hparent, hchild, pow_succ, mul_neg_one,
    rectangleAverageSum_parent_insert S A j hj hjA Q,
    rectangleAverageSum_child_insert S A j hj hjA Q]
  let C : Module.End ℝ (boundedMeasurableFunctions d) :=
    ∑ P ∈ (Prepartition.splitCenter (Q j)).boxes, averageMap j P
  let P : Module.End ℝ (boundedMeasurableFunctions d) := averageMap j (Q j)
  let T := rectangleAverageSum S A Q
  let c : ℝ := (-1 : ℝ) ^ (S.card - A.card)
  change (-c) • (P * T) + c • (C * T) = (C - P) * (c • T)
  apply LinearMap.ext
  intro F
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
    LinearMap.sub_apply, LinearMap.map_smul]
  rw [neg_smul]
  rw [sub_eq_add_neg, add_comm]

private theorem productDifferenceMap_expansion
    (S : Finset (Fin m)) (Q : ∀ i, Box (Fin (d i))) :
    productDifferenceMap S Q = differenceExpansion S Q := by
  induction S using Finset.induction_on with
  | empty =>
      simp [differenceExpansion, rectangleAverageSum, differenceRectangles]
  | @insert j S hj ih =>
      rw [productDifferenceMap_insert S j hj, differenceExpansion_insert S j hj, ih]

/-- The signed rectangle-integral expansion equals the product of coordinate
differences on every bounded measurable input. -/
theorem rawProductDifference_eq_productDifferenceMap
    (Q : ∀ i, Box (Fin (d i))) (F : boundedMeasurableFunctions d) :
    rawProductDifference Q F.1 = (productDifferenceMap Finset.univ Q F).1 := by
  funext x
  have h := congrArg
    (fun T : Module.End ℝ (boundedMeasurableFunctions d) => (T F).1 x)
    (productDifferenceMap_expansion Finset.univ Q)
  simpa [differenceExpansion, rectangleAverageSum, rawProductDifference,
    Finset.sum_apply, productAverageMap_univ_eq_integral] using h.symm

end ReyZygmund.Geometry
