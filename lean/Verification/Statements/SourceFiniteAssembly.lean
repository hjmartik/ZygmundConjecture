import ReyZygmund.Geometry.GridFamilies
import ReyZygmund.Geometry.FiniteSquare
import ReyZygmund.Projection.CommonProjection
import ReyZygmund.Maximal.GeneralInput
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Finite statements at a common smallest scale

Nonemptiness and the geometric hypotheses imply compatibility of the top cubes
with the smallest scale. The conclusions identify the finite step-function
representative and establish integrability. Both estimates use the
supported-integral maximal function and extended Lp norms. The representation and
reduction proofs are not imported.


-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry ReyZygmund.Projection

def sourceRepresentationContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m → (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
      (I : ∀ i, Box (Fin (d i))), (∀ i, I i ∈ (D i).cubes (n i)) →
    ∀ G : Finset (∀ i, Box (Fin (d i))), G.Nonempty →
      (∀ R ∈ G, R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
        ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u) →
      (∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → R = S) →
    ∀ f : ProductPoint d → ℝ,
      (∀ x, x ∉ productBox I → f x = 0) →
      (∀ x ∈ productBox I, 0 < f x) →
      (∀ R, (R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
        ∀ i u, (R i).upper u - (R i).lower u = (2 : ℝ) ^ (-k)) →
        ∀ x ∈ productBox R, ∀ y ∈ productBox R, f x = f y) →
      let N : Fin m → ℕ := fun i => (k - n i).toNat
      ∃ hleaf : ProductLeafConstant I N f,
        let f₀ := finiteInput I N f hleaf
        let F := finiteProjectionMap I N G f₀
        f₀.1 = f ∧
        IntegrableOn f (productBox I) ∧
        IntegrableOn F.1 (productBox I) ∧
        ∀ R ∈ averagingRectangles I N G,
          (∫ y in productBox R, F.1 y) / volume.real (productBox R) =
            (∫ y in productBox R, f y) / volume.real (productBox R) ∧
          ∀ x ∈ productBox R,
            (∫ y in productBox R, f y) / volume.real (productBox R) =
              ∑ B ∈ ((Finset.univ : Finset (Fin m)).powerset.erase Finset.univ),
                (-1 : ℝ) ^ (m + 1 + B.card) * (productAverageMap B R F).1 x

def sourceMaximalToSquareContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m → (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
      (I : ∀ i, Box (Fin (d i))), (∀ i, I i ∈ (D i).cubes (n i)) →
    ∀ G : Finset (∀ i, Box (Fin (d i))), G.Nonempty →
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
      let N : Fin m → ℕ := fun i => (k - n i).toNat
      ∃ hleaf : ProductLeafConstant I N f,
        let f₀ := finiteInput I N f hleaf
        let F := finiteProjectionMap I N G f₀
        let M := finiteFunctionMaximal (averagingRectangles I N G) f
        let W := finiteComplementSquareFunction I N F
        let C := (m : ℝ) * (2 : ℝ) ^ m *
          ((2 : ℝ) ^ (6 * (∑ i, d i) + 10) + (2 : ℝ) ^ (m - 1))
        f₀.1 = f ∧
        MemLp f (ENNReal.ofReal p) (volume.restrict (productBox I)) ∧
        MemLp M (ENNReal.ofReal p) (volume.restrict (productBox I)) ∧
        MemLp W (ENNReal.ofReal p) (volume.restrict (productBox I)) ∧
        eLpNorm M (ENNReal.ofReal p) (volume.restrict (productBox I)) ≤
          ENNReal.ofReal (C * (p / (p - 1)) ^ (m - 2)) *
            eLpNorm f (ENNReal.ofReal p) (volume.restrict (productBox I)) +
          ENNReal.ofReal C *
            eLpNorm W (ENNReal.ofReal p) (volume.restrict (productBox I))

def sourceHolderAbsorptionContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m → (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
      (I : ∀ i, Box (Fin (d i))), (∀ i, I i ∈ (D i).cubes (n i)) →
    ∀ G : Finset (∀ i, Box (Fin (d i))), G.Nonempty →
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
      let N : Fin m → ℕ := fun i => (k - n i).toNat
      ∃ hleaf : ProductLeafConstant I N f,
        let f₀ := finiteInput I N f hleaf
        let F := finiteProjectionMap I N G f₀
        let M := finiteFunctionMaximal (averagingRectangles I N G) f
        let W := finiteComplementSquareFunction I N F
        let C := Real.sqrt ((m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)))
        f₀.1 = f ∧
        MemLp f (ENNReal.ofReal p) (volume.restrict (productBox I)) ∧
        MemLp M (ENNReal.ofReal p) (volume.restrict (productBox I)) ∧
        MemLp W (ENNReal.ofReal p) (volume.restrict (productBox I)) ∧
        eLpNorm W (ENNReal.ofReal p) (volume.restrict (productBox I)) ≤
          ENNReal.ofReal (C * Real.rpow (p - 1) (-((m - 1 : ℕ) : ℝ) / 2)) *
            (eLpNorm f (ENNReal.ofReal p) (volume.restrict (productBox I))) ^ (p / 2) *
            (eLpNorm M (ENNReal.ofReal p) (volume.restrict (productBox I))) ^ (1 - p / 2)

end ReyZygmundVerification
