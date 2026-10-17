import ReyZygmund.Geometry.FiniteSetting
import ReyZygmund.Geometry.ProductMaps
import ReyZygmund.Geometry.ProductContainment
import ReyZygmund.Geometry.PartialIndices
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! # Finite products with a common smallest scale

The top cubes may have different side lengths. Their finite subdivision depths
are chosen separately, so that every bottom cube has the prescribed side length.
A partial tuple is completed by the top cubes in the unselected coordinates;
this identifies the partial indices with the finite tuples used in the sums.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.Geometry

open MathlibOnly (CubeGrid Rectangle PartialRectangle bottomCubes ConstantOnBottomRectangles)

variable {m : ℕ} {d : Fin m → ℕ}

/-- Bottom rectangles are products of the last subdivisions of the top cubes. -/
theorem mem_productLeaves_iff_bottomCubes
    (D : ∀ i, CubeGrid (d i)) {I : Rectangle d} {l : Fin m → ℤ} {k : ℤ}
    (hI : ∀ i, I i ∈ (D i).cubes (l i)) (hcut : ∀ i, -k ≤ l i)
    (Q : Rectangle d) :
    Q ∈ productLeaves I (fun i => (l i + k).toNat) ↔
      ∀ i, Q i ∈ bottomCubes (D i) (I i) k := by
  rw [productLeaves, Fintype.mem_piFinset]
  apply forall_congr'
  intro i
  rw [bottomCubes_eq_leaves (D i) (hI i) (hcut i)]
  rfl

/-- The common scale gives exactly the product-leaf constancy condition. -/
theorem constantOnBottomRectangles_iff
    (D : ∀ i, CubeGrid (d i)) {I : Rectangle d} {l : Fin m → ℤ} {k : ℤ}
    (hI : ∀ i, I i ∈ (D i).cubes (l i)) (hcut : ∀ i, -k ≤ l i)
    (f : ProductPoint d → ℝ) :
    ConstantOnBottomRectangles D I k f ↔
      ProductLeafConstant I (fun i => (l i + k).toNat) f := by
  unfold ConstantOnBottomRectangles ProductLeafConstant
  simp_rw [mem_productLeaves_iff_bottomCubes D hI hcut]

/-- The bottom generation is the same in every coordinate, although the depths
below the top cubes may differ. -/
theorem common_cutoff_productLeaves_iff
    (D : ∀ i, CubeGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : Rectangle d) (hI : ∀ i, I i ∈ (D i).cubesAtGeneration (n i))
    (hnk : ∀ i, n i ≤ k) (R : Rectangle d) :
    R ∈ productLeaves I (fun i => (k - n i).toNat) ↔
      (∀ i, R i ∈ (D i).cubesAtGeneration k) ∧
        productRectangle R ⊆ productRectangle I := by
  have h := mem_productLeaves_iff_bottomCubes D hI
    (fun i => show -k ≤ -n i by have hi := hnk i; omega) R
  rw [productRectangle_subset_iff]
  simpa only [sub_eq_add_neg, add_comm, bottomCubes, Set.mem_ofPred_eq,
    MathlibOnly.CubeGrid.cubesAtGeneration, forall_and, Box.coe_subset_coe] using h

/-- Insert the top factors in the unselected coordinates. -/
def completePartialRectangle (I : Rectangle d) (A : Finset (Fin m))
    (K : PartialRectangle d A) : Rectangle d :=
  fun i => if hi : i ∈ A then K ⟨i, hi⟩ else I i

@[simp] theorem completePartialRectangle_selected
    (I : Rectangle d) (A : Finset (Fin m)) (K : PartialRectangle d A) (i : A) :
    completePartialRectangle I A K i = K i := by
  simp [completePartialRectangle]

@[simp] theorem completePartialRectangle_unselected
    (I : Rectangle d) (A : Finset (Fin m)) (K : PartialRectangle d A)
    {i : Fin m} (hi : i ∉ A) : completePartialRectangle I A K i = I i := by
  simp [completePartialRectangle, hi]

/-- Completing a partial tuple gives its mixed integration region. -/
theorem partialRectangle_eq_productRectangle
    (I : Rectangle d) (A : Finset (Fin m)) (K : PartialRectangle d A) :
    MathlibOnly.partialRectangleRegion I A K = productRectangle (completePartialRectangle I A K) := by
  ext x
  simp only [MathlibOnly.partialRectangleRegion, productRectangle, Set.mem_ofPred_eq]
  apply forall_congr'
  intro i
  by_cases hi : i ∈ A <;> simp [completePartialRectangle, hi]

/-- Restricting a finite partial index and then completing it recovers that index. -/
theorem completePartialRectangle_restrict
    (I : Rectangle d) (N : Fin m → ℕ) (A : Finset (Fin m))
    {Q : Rectangle d} (hQ : Q ∈ partialInterior I N A) :
    completePartialRectangle I A (fun i : A => Q i) = Q := by
  funext i
  by_cases hi : i ∈ A
  · simp [completePartialRectangle, hi]
  · simp [completePartialRectangle, hi, partialInterior_mem_unselected hQ hi]

/-- Interior indices in the selected coordinates have exactly one completion. -/
theorem completePartialRectangle_mem_iff
    (D : ∀ i, CubeGrid (d i)) {I : Rectangle d} {l : Fin m → ℤ} {k : ℤ}
    (hI : ∀ i, I i ∈ (D i).cubes (l i)) (hcut : ∀ i, -k ≤ l i)
    (A : Finset (Fin m)) (hd : ∀ i ∈ A, 0 < d i) (K : PartialRectangle d A) :
    completePartialRectangle I A K ∈ partialInterior I (fun i => (l i + k).toNat) A ↔
      K ∈ MathlibOnly.partialInterior D I k A := by
  rw [partialInterior, Fintype.mem_piFinset]
  constructor
  · intro h i
    have hi := h i
    simpa only [i.property, ite_true, completePartialRectangle_selected,
      interiorCubes_eq_interior (D i) (hd i i.property) (hI i) (hcut i), Finset.mem_coe] using hi
  · intro h i
    by_cases hi : i ∈ A
    · have hk := h ⟨i, hi⟩
      simpa only [hi, ite_true, completePartialRectangle, dite_eq_left,
        interiorCubes_eq_interior (D i) (hd i hi) (hI i) (hcut i), Finset.mem_coe] using hk
    · simp [completePartialRectangle, hi]

/-- The partial tuples and their finite completions index the same sum. -/
noncomputable def partialInteriorEquiv
    (D : ∀ i, CubeGrid (d i)) {I : Rectangle d} {l : Fin m → ℤ} {k : ℤ}
    (hI : ∀ i, I i ∈ (D i).cubes (l i)) (hcut : ∀ i, -k ≤ l i)
    (A : Finset (Fin m)) (hd : ∀ i ∈ A, 0 < d i) :
    MathlibOnly.partialInterior D I k A ≃ partialInterior I (fun i => (l i + k).toNat) A where
  toFun K := ⟨completePartialRectangle I A K.1,
    (completePartialRectangle_mem_iff D hI hcut A hd K.1).mpr K.2⟩
  invFun Q := ⟨fun i : A => Q.1 i,
    (completePartialRectangle_mem_iff D hI hcut A hd _).mp
      (by rw [completePartialRectangle_restrict I _ A Q.2]; exact Q.2)⟩
  left_inv K := by
    apply Subtype.ext
    funext i
    exact completePartialRectangle_selected I A K.1 i
  right_inv Q := Subtype.ext (completePartialRectangle_restrict I _ A Q.2)

/-- A sum over the public partial indices is the corresponding finite sum,
without multiplicities from the unselected coordinates. -/
theorem tsum_partialInterior_eq
    (D : ∀ i, CubeGrid (d i)) {I : Rectangle d} {l : Fin m → ℤ} {k : ℤ}
    (hI : ∀ i, I i ∈ (D i).cubes (l i)) (hcut : ∀ i, -k ≤ l i)
    (A : Finset (Fin m)) (hd : ∀ i ∈ A, 0 < d i)
    (F : PartialRectangle d A → ℝ≥0∞) :
    (∑' K : MathlibOnly.partialInterior D I k A, F K.1) =
      ∑ Q ∈ partialInterior I (fun i => (l i + k).toNat) A, F (fun i : A => Q i) := by
  calc
    _ = ∑' Q : partialInterior I (fun i => (l i + k).toNat) A,
        F (fun i : A => Q.1 i) :=
      ((partialInteriorEquiv D hI hcut A hd).symm.tsum_eq (fun K => F K.1)).symm
    _ = _ := Finset.tsum_subtype' (partialInterior I (fun i => (l i + k).toNat) A)
      (fun Q => F (fun i : A => Q i))

end ReyZygmund.Geometry
