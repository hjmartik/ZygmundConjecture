import ReyZygmund.Geometry.CoordinateFibre
import ReyZygmund.Geometry.FiniteSquare
import ReyZygmund.Maximal.PartialSigned

/-! # Products of operators on a fixed-coordinate slice

Slicing a bounded measurable function commutes with the coordinate products.
Inserting the omitted top cube gives a bijection of the partial indices. Deleting
the unused coordinate preserves the signed maximum, since repeated candidates do
not affect a supremum. These pointwise identities are used in the maximal–square
estimate.


-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

open Projection

variable {n : ℕ} {d : Fin (n + 1) → ℕ}

/-- Slicing preserves the bound and measurability of a bounded measurable function,
with no support or step-function hypothesis. -/
noncomputable def coordinateFibreMap
    (j : Fin (n + 1)) (t : Fin (d j) → ℝ) :
    boundedMeasurableFunctions d →ₗ[ℝ]
      boundedMeasurableFunctions (fun i => d (j.succAbove i)) where
  toFun F := ⟨fun y => F.1 (j.insertNth t y),
    F.2.1.comp (measurable_coordinateFibre_insertNth j t), by
      obtain ⟨C, hC, hF⟩ := F.2.2
      exact ⟨C, hC, fun y => hF (j.insertNth t y)⟩⟩
  map_add' F G := by
    apply Subtype.ext
    rfl
  map_smul' c F := by
    apply Subtype.ext
    rfl

@[simp] theorem coordinateFibreMap_apply
    (j : Fin (n + 1)) (t : Fin (d j) → ℝ)
    (F : boundedMeasurableFunctions d)
    (y : ProductPoint (fun i => d (j.succAbove i))) :
    (coordinateFibreMap j t F).1 y = F.1 (j.insertNth t y) := rfl

theorem coordinateFibreMap_averageMap
    (j : Fin (n + 1)) (t : Fin (d j) → ℝ) (i : Fin n)
    (Q : Box (Fin (d (j.succAbove i)))) (F : boundedMeasurableFunctions d) :
    coordinateFibreMap j t (averageMap (j.succAbove i) Q F) =
      averageMap i Q (coordinateFibreMap j t F) := by
  apply Subtype.ext
  funext y
  exact (coordinateAverage_insertNth j t i Q F.1 y).symm

theorem coordinateFibreMap_differenceMap
    (j : Fin (n + 1)) (t : Fin (d j) → ℝ) (i : Fin n)
    (Q : Box (Fin (d (j.succAbove i)))) (F : boundedMeasurableFunctions d) :
    coordinateFibreMap j t (differenceMap (j.succAbove i) Q F) =
      differenceMap i Q (coordinateFibreMap j t F) := by
  apply Subtype.ext
  funext y
  simp only [coordinateFibreMap_apply, differenceMap_apply]
  change coordinateDifference (j.succAbove i) Q F.1 (j.insertNth t y) =
    coordinateDifference i Q (fun z => F.1 (j.insertNth t z)) y
  exact (coordinateDifference_insertNth j t i Q F.1 y).symm

/-- Products over corresponding selected coordinates have exactly the same
fibre values. The empty product is included. -/
theorem coordinateFibreMap_productAverageMap_image
    (j : Fin (n + 1)) (t : Fin (d j) → ℝ) (A : Finset (Fin n))
    (Q : ∀ i, Box (Fin (d i))) (F : boundedMeasurableFunctions d) :
    coordinateFibreMap j t (productAverageMap (A.image j.succAbove) Q F) =
      productAverageMap A (fun i => Q (j.succAbove i)) (coordinateFibreMap j t F) := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
    have hi' : j.succAbove i ∉ A.image j.succAbove := by
      intro h
      obtain ⟨k, hk, hki⟩ := Finset.mem_image.mp h
      exact hi (Fin.succAbove_right_injective hki ▸ hk)
    rw [Finset.image_insert, productAverageMap_insert _ _ hi',
      productAverageMap_insert _ _ hi, Module.End.mul_apply, Module.End.mul_apply,
      coordinateFibreMap_averageMap, ih]

theorem coordinateFibreMap_productDifferenceMap_image
    (j : Fin (n + 1)) (t : Fin (d j) → ℝ) (A : Finset (Fin n))
    (Q : ∀ i, Box (Fin (d i))) (F : boundedMeasurableFunctions d) :
    coordinateFibreMap j t (productDifferenceMap (A.image j.succAbove) Q F) =
      productDifferenceMap A (fun i => Q (j.succAbove i)) (coordinateFibreMap j t F) := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
    have hi' : j.succAbove i ∉ A.image j.succAbove := by
      intro h
      obtain ⟨k, hk, hki⟩ := Finset.mem_image.mp h
      exact hi (Fin.succAbove_right_injective hki ▸ hk)
    rw [Finset.image_insert, productDifferenceMap_insert _ _ hi',
      productDifferenceMap_insert _ _ hi, Module.End.mul_apply, Module.End.mul_apply,
      coordinateFibreMap_differenceMap, ih]

theorem coordinateFibreMap_productAverageMap_erase
    (j : Fin (n + 1)) (t : Fin (d j) → ℝ)
    (Q : ∀ i, Box (Fin (d i))) (F : boundedMeasurableFunctions d) :
    coordinateFibreMap j t (productAverageMap (Finset.univ.erase j) Q F) =
      productAverageMap Finset.univ (fun i => Q (j.succAbove i))
        (coordinateFibreMap j t F) := by
  simpa only [Fin.image_succAbove_univ, Finset.compl_singleton] using
    coordinateFibreMap_productAverageMap_image j t Finset.univ Q F

theorem coordinateFibreMap_productDifferenceMap_erase
    (j : Fin (n + 1)) (t : Fin (d j) → ℝ)
    (Q : ∀ i, Box (Fin (d i))) (F : boundedMeasurableFunctions d) :
    coordinateFibreMap j t (productDifferenceMap (Finset.univ.erase j) Q F) =
      productDifferenceMap Finset.univ (fun i => Q (j.succAbove i))
        (coordinateFibreMap j t F) := by
  simpa only [Fin.image_succAbove_univ, Finset.compl_singleton] using
    coordinateFibreMap_productDifferenceMap_image j t Finset.univ Q F

/-- Inserting the omitted top cube gives a bijection of indices. The unused coordinate
introduces neither a depth factor nor an empty index set. -/
theorem partialInterior_erase_eq_image_insertNth
    (I : ∀ i, Box (Fin (d i))) (N : Fin (n + 1) → ℕ) (j : Fin (n + 1)) :
    partialInterior I N (Finset.univ.erase j) =
      (productInterior (fun i => I (j.succAbove i)) (fun i => N (j.succAbove i))).image
        (fun Q => j.insertNth (α := fun i => Box (Fin (d i))) (I j) Q) := by
  ext Q
  constructor
  · intro hQ
    apply Finset.mem_image.mpr
    refine ⟨j.removeNth Q, ?_, ?_⟩
    · apply mem_productInterior.mpr
      intro i
      exact partialInterior_mem_selected hQ
        (Finset.mem_erase.mpr ⟨Fin.succAbove_ne j i, Finset.mem_univ _⟩)
    · apply Fin.insertNth_eq_iff.mpr
      exact ⟨(partialInterior_mem_unselected hQ (by simp)).symm, rfl⟩
  · intro hQ
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hQ
    apply Fintype.mem_piFinset.mpr
    refine j.forall_iff_succAbove.mpr ⟨?_, ?_⟩
    · simp only [Finset.notMem_erase, ite_false, Fin.insertNth_apply_same,
        Finset.mem_singleton]
    · intro i
      have hi : j.succAbove i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j := by
        simp
      simpa only [hi, ite_true, Fin.insertNth_apply_succAbove] using
        mem_productInterior.mp hR i

/-- Finite sums count each reduced interior tuple once. -/
theorem sum_partialInterior_erase_insertNth {V : Type*} [AddCommMonoid V]
    (I : ∀ i, Box (Fin (d i))) (N : Fin (n + 1) → ℕ) (j : Fin (n + 1))
    (H : (∀ i, Box (Fin (d i))) → V) :
    (∑ Q ∈ partialInterior I N (Finset.univ.erase j), H Q) =
      ∑ Q ∈ productInterior (fun i => I (j.succAbove i)) (fun i => N (j.succAbove i)),
        H (j.insertNth (I j) Q) := by
  rw [partialInterior_erase_eq_image_insertNth]
  apply Finset.sum_image
  intro Q _ R _ h
  exact (Fin.insertNth_inj.mp h).2

/-- Slicing turns the partial difference sum into the full difference sum in the
remaining coordinates, without a finite step-function hypothesis. -/
theorem coordinateFibreMap_difference_sum
    (I : ∀ i, Box (Fin (d i))) (N : Fin (n + 1) → ℕ)
    (j : Fin (n + 1)) (t : Fin (d j) → ℝ) (F : boundedMeasurableFunctions d) :
    coordinateFibreMap j t
        (∑ Q ∈ partialInterior I N (Finset.univ.erase j),
          productDifferenceMap (Finset.univ.erase j) Q F) =
      ∑ Q ∈ productInterior (fun i => I (j.succAbove i)) (fun i => N (j.succAbove i)),
        productDifferenceMap Finset.univ Q (coordinateFibreMap j t F) := by
  rw [map_sum, sum_partialInterior_erase_insertNth]
  apply Finset.sum_congr rfl
  intro Q _
  simpa only [Fin.insertNth_apply_succAbove] using
    coordinateFibreMap_productDifferenceMap_erase j t (j.insertNth (I j) Q) F

/-- The partial square function equals the full square function on
the remaining Euclidean coordinates, at every fibre point. -/
theorem finiteSquareFunction_coordinateFibre
    (I : ∀ i, Box (Fin (d i))) (N : Fin (n + 1) → ℕ)
    (j : Fin (n + 1)) (t : Fin (d j) → ℝ) (F : boundedMeasurableFunctions d)
    (y : ProductPoint (fun i => d (j.succAbove i))) :
    finiteSquareFunction I N (Finset.univ.erase j) F (j.insertNth t y) =
      finiteSquareFunction (fun i => I (j.succAbove i)) (fun i => N (j.succAbove i))
        Finset.univ (coordinateFibreMap j t F) y := by
  have hidx : partialInterior (fun i => I (j.succAbove i))
      (fun i => N (j.succAbove i)) Finset.univ =
      productInterior (fun i => I (j.succAbove i)) (fun i => N (j.succAbove i)) := by
    simp only [partialInterior, productInterior, Finset.mem_univ, ite_true]
  unfold finiteSquareFunction
  apply congrArg Real.sqrt
  rw [sum_partialInterior_erase_insertNth, hidx]
  apply Finset.sum_congr rfl
  intro Q _
  have h := congrArg
    (fun G : boundedMeasurableFunctions (fun i => d (j.succAbove i)) => G.1 y)
    (coordinateFibreMap_productDifferenceMap_erase j t (j.insertNth (I j) Q) F)
  apply congrArg (fun z : ℝ => z ^ 2)
  simpa only [coordinateFibreMap_apply, Fin.insertNth_apply_succAbove] using h

/-- Deleting the unused coordinate preserves the finite signed maximum; inserting its
top cube gives the reverse inequality. The absolute value stays outside each
signed average. -/
theorem finiteSignedPartialMaximal_coordinateFibre
    (I : ∀ i, Box (Fin (d i))) (N : Fin (n + 1) → ℕ)
    (j : Fin (n + 1)) (t : Fin (d j) → ℝ) (F : boundedMeasurableFunctions d)
    (y : ProductPoint (fun i => d (j.succAbove i))) :
    finiteSignedPartialMaximal I N (Finset.univ.erase j) F (j.insertNth t y) =
      finiteSignedProductMaximal (fun i => I (j.succAbove i)) (fun i => N (j.succAbove i))
        (coordinateFibreMap j t F) y := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro Q hQ
    have hQ' : (fun i => Q (j.succAbove i)) ∈
        productDescendants (fun i => I (j.succAbove i)) (fun i => N (j.succAbove i)) :=
      mem_productDescendants.mpr (fun i => mem_productDescendants.mp hQ (j.succAbove i))
    change |(productAverageMap (Finset.univ.erase j) Q F).1 (j.insertNth t y)| ≤ _
    rw [← coordinateFibreMap_apply j t (productAverageMap (Finset.univ.erase j) Q F) y,
      coordinateFibreMap_productAverageMap_erase]
    exact Finset.le_sup'
      (fun R => |(productAverageMap Finset.univ R (coordinateFibreMap j t F)).1 y|) hQ'
  · apply Finset.sup'_le
    intro Q hQ
    have hR : j.insertNth (I j) Q ∈ productDescendants I N := by
      apply mem_productDescendants.mpr
      refine j.forall_iff_succAbove.mpr ⟨?_, ?_⟩
      · simpa only [Fin.insertNth_apply_same] using
          mem_productDescendants.mp (root_mem_productDescendants I N) j
      · intro i
        simpa only [Fin.insertNth_apply_succAbove] using mem_productDescendants.mp hQ i
    have heq :
        (productAverageMap (Finset.univ.erase j) (j.insertNth (I j) Q) F).1
            (j.insertNth t y) =
          (productAverageMap Finset.univ Q (coordinateFibreMap j t F)).1 y := by
      simpa only [coordinateFibreMap_apply, Fin.insertNth_apply_succAbove] using
        congrArg (fun G : boundedMeasurableFunctions (fun i => d (j.succAbove i)) => G.1 y)
          (coordinateFibreMap_productAverageMap_erase j t (j.insertNth (I j) Q) F)
    change |(productAverageMap Finset.univ Q (coordinateFibreMap j t F)).1 y| ≤ _
    rw [← heq]
    exact Finset.le_sup'
      (fun R => |(productAverageMap (Finset.univ.erase j) R F).1 (j.insertNth t y)|) hR

end ReyZygmund.Geometry
