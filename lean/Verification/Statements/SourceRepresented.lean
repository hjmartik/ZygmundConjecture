import ReyZygmund.Geometry.GridFamilies
import ReyZygmund.Maximal.GeneralInput
import ReyZygmund.Maximal.Constants
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # The maximal statement at a common smallest scale

The conclusion uses the extended Lp norm even when an incompatible smallest scale
forces the original family to be empty. In that case the input need not be
integrable. The intermediate real-integral statement is recorded separately. The
proof of the maximal conclusion is not imported.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

open ReyZygmund.MathlibOnly (CubeGrid gridRectangles)

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry

def sourceFiniteIncomparableMaximalNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m → (∀ i, 0 < d i) →
    ∀ (D : ∀ i, CubeGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
      (I : ∀ i, Box (Fin (d i))), (∀ i, I i ∈ (D i).cubesAtGeneration (n i)) →
    ∀ G : Finset (∀ i, Box (Fin (d i))),
      (∀ R ∈ G, R ∈ gridRectangles D ∧ productRectangle R ⊆ productRectangle I ∧
        ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u) →
      (∀ R ∈ G, ∀ S ∈ G, productRectangle R ⊆ productRectangle S → R = S) →
    ∀ f : ProductPoint d → ℝ,
      (∀ x, x ∉ productRectangle I → f x = 0) →
      (∀ x ∈ productRectangle I, 0 < f x) →
      (∀ R, (R ∈ gridRectangles D ∧ productRectangle R ⊆ productRectangle I ∧
        ∀ i u, (R i).upper u - (R i).lower u = (2 : ℝ) ^ (-k)) →
        ∀ x ∈ productRectangle R, ∀ y ∈ productRectangle R, f x = f y) →
    ∀ p : ℝ, 1 < p → p ≤ (3 : ℝ) / 2 →
      eLpNorm (finiteFunctionMaximal G f) (ENNReal.ofReal p)
        (volume.restrict (productRectangle I)) ≤
      ENNReal.ofReal (maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1)) *
        eLpNorm f (ENNReal.ofReal p) (volume.restrict (productRectangle I))

def sourceFiniteIncomparableMaximalIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m → (∀ i, 0 < d i) →
    ∀ (D : ∀ i, CubeGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
      (I : ∀ i, Box (Fin (d i))), (∀ i, I i ∈ (D i).cubesAtGeneration (n i)) →
    ∀ G : Finset (∀ i, Box (Fin (d i))),
      (∀ R ∈ G, R ∈ gridRectangles D ∧ productRectangle R ⊆ productRectangle I ∧
        ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u) →
      (∀ R ∈ G, ∀ S ∈ G, productRectangle R ⊆ productRectangle S → R = S) →
    ∀ f : ProductPoint d → ℝ,
      (∀ x, x ∉ productRectangle I → f x = 0) →
      (∀ x ∈ productRectangle I, 0 < f x) →
      (∀ R, (R ∈ gridRectangles D ∧ productRectangle R ⊆ productRectangle I ∧
        ∀ i u, (R i).upper u - (R i).lower u = (2 : ℝ) ^ (-k)) →
        ∀ x ∈ productRectangle R, ∀ y ∈ productRectangle R, f x = f y) →
    ∀ p : ℝ, 1 < p → p ≤ (3 : ℝ) / 2 →
      Real.rpow (∫ x in productRectangle I, Real.rpow (finiteFunctionMaximal G f x) p)
        (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productRectangle I, Real.rpow (f x) p) (1 / p)

end ReyZygmundVerification
