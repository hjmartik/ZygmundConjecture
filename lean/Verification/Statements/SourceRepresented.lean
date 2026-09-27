import ReyZygmund.Geometry.GridFamilies
import ReyZygmund.Maximal.GeneralInput
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # The maximal statement at a common smallest scale

The conclusion uses the extended Lp norm even when an incompatible smallest scale
forces the original family to be empty. In that case the input need not be
integrable. The intermediate real-integral statement is recorded separately. The
proof of the maximal conclusion is not imported.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry

def sourceFiniteIncomparableMaximalNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m → (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
      (I : ∀ i, Box (Fin (d i))), (∀ i, I i ∈ (D i).cubes (n i)) →
    ∀ G : Finset (∀ i, Box (Fin (d i))),
      (∀ R ∈ G, R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
        ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u) →
      (∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → R = S) →
    ∀ f : ProductPoint d → ℝ,
      (∀ x, x ∉ productBox I → f x = 0) →
      (∀ x ∈ productBox I, 0 < f x) →
      (∀ R, (R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
        ∀ i u, (R i).upper u - (R i).lower u = (2 : ℝ) ^ (-k)) →
        ∀ x ∈ productBox R, ∀ y ∈ productBox R, f x = f y) →
    ∀ p : ℝ, 1 < p → p ≤ (3 : ℝ) / 2 →
      eLpNorm (finiteFunctionMaximal G f) (ENNReal.ofReal p)
        (volume.restrict (productBox I)) ≤
      ENNReal.ofReal (maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1)) *
        eLpNorm f (ENNReal.ofReal p) (volume.restrict (productBox I))

def sourceFiniteIncomparableMaximalIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m → (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
      (I : ∀ i, Box (Fin (d i))), (∀ i, I i ∈ (D i).cubes (n i)) →
    ∀ G : Finset (∀ i, Box (Fin (d i))),
      (∀ R ∈ G, R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
        ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u) →
      (∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → R = S) →
    ∀ f : ProductPoint d → ℝ,
      (∀ x, x ∉ productBox I → f x = 0) →
      (∀ x ∈ productBox I, 0 < f x) →
      (∀ R, (R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
        ∀ i u, (R i).upper u - (R i).lower u = (2 : ℝ) ^ (-k)) →
        ∀ x ∈ productBox R, ∀ y ∈ productBox R, f x = f y) →
    ∀ p : ℝ, 1 < p → p ≤ (3 : ℝ) / 2 →
      Real.rpow (∫ x in productBox I, Real.rpow (finiteFunctionMaximal G f x) p)
        (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p)

end ReyZygmundVerification
