import ReyZygmund.Geometry.GridFamilies
import ReyZygmund.Geometry.ProductContainment

/-! Statements relating the common smallest side length to the coordinate depths. The
proof module is not imported. -/

open BoxIntegral
open scoped Classical

open ReyZygmund.MathlibOnly (CubeGrid gridRectangles)

namespace ReyZygmundVerification

open ReyZygmund.Geometry ReyZygmund.Projection

def sourceProductDescendantsContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ), (∀ i, 0 < d i) →
    ∀ (D : ∀ i, CubeGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
      (I : ∀ i, Box (Fin (d i))), (∀ i, I i ∈ (D i).cubesAtGeneration (n i)) →
      (∀ i, n i ≤ k) → ∀ (R : ∀ i, Box (Fin (d i))),
        R ∈ productDescendants I (fun i => (k - n i).toNat) ↔
          R ∈ gridRectangles D ∧ productRectangle R ⊆ productRectangle I ∧
            ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u

def sourceProductInteriorContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ), (∀ i, 0 < d i) →
    ∀ (D : ∀ i, CubeGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
      (I : ∀ i, Box (Fin (d i))), (∀ i, I i ∈ (D i).cubesAtGeneration (n i)) →
      (∀ i, n i ≤ k) → ∀ (R : ∀ i, Box (Fin (d i))),
        R ∈ productInterior I (fun i => (k - n i).toNat) ↔
          R ∈ gridRectangles D ∧ productRectangle R ⊆ productRectangle I ∧
            ∀ i u, (2 : ℝ) ^ (-k) < (R i).upper u - (R i).lower u

def sourceProductLeavesContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ), (∀ i, 0 < d i) →
    ∀ (D : ∀ i, CubeGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
      (I : ∀ i, Box (Fin (d i))), (∀ i, I i ∈ (D i).cubesAtGeneration (n i)) →
      (∀ i, n i ≤ k) → ∀ (R : ∀ i, Box (Fin (d i))),
        R ∈ productLeaves I (fun i => (k - n i).toNat) ↔
          R ∈ gridRectangles D ∧ productRectangle R ⊆ productRectangle I ∧
            ∀ i u, (R i).upper u - (R i).lower u = (2 : ℝ) ^ (-k)

def sourceProductLeafConstantContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ), (∀ i, 0 < d i) →
    ∀ (D : ∀ i, CubeGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
      (I : ∀ i, Box (Fin (d i))), (∀ i, I i ∈ (D i).cubesAtGeneration (n i)) →
      (∀ i, n i ≤ k) → ∀ (f : ProductPoint d → ℝ),
        ProductLeafConstant I (fun i => (k - n i).toNat) f ↔
          ∀ R, (R ∈ gridRectangles D ∧ productRectangle R ⊆ productRectangle I ∧
            ∀ i u, (R i).upper u - (R i).lower u = (2 : ℝ) ^ (-k)) →
            ∀ x ∈ productRectangle R, ∀ y ∈ productRectangle R, f x = f y

def sourceCutoffOrEmptyContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ), (∀ i, 0 < d i) →
    ∀ (D : ∀ i, CubeGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
      (I : ∀ i, Box (Fin (d i))), (∀ i, I i ∈ (D i).cubesAtGeneration (n i)) →
      ∀ (G : Finset (∀ i, Box (Fin (d i)))),
        (∀ R ∈ G, R ∈ gridRectangles D ∧ productRectangle R ⊆ productRectangle I ∧
          ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u) →
        (∀ i, n i ≤ k) ∨ G = ∅

end ReyZygmundVerification
