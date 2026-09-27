import ReyZygmund.Geometry.ProductLp

/-! Exact power-integral norm interfaces for finite top rectangles. -/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal
open ReyZygmund.Geometry

namespace ReyZygmundVerification

def productLeafMemLpContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ), ProductLeafConstant I N f →
  ∀ (p : ℝ), 0 < p →
    MemLp f (ENNReal.ofReal p) (volume.restrict (productBox I))

def productLeafLpNormIdentityContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ), ProductLeafConstant I N f →
  ∀ (p : ℝ), 0 < p →
    lpNorm f (ENNReal.ofReal p) (volume.restrict (productBox I)) =
      Real.rpow (∫ x in productBox I, Real.rpow |f x| p) (1 / p)

def rootLpAddContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f g : ProductPoint d → ℝ),
    ProductLeafConstant I N f → ProductLeafConstant I N g →
  ∀ (p : ℝ), 1 ≤ p →
    Real.rpow (∫ x in productBox I, Real.rpow |f x + g x| p) (1 / p) ≤
      Real.rpow (∫ x in productBox I, Real.rpow |f x| p) (1 / p) +
        Real.rpow (∫ x in productBox I, Real.rpow |g x| p) (1 / p)

def rootLpSumContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} {α : Type*}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (s : Finset α) (f : α → ProductPoint d → ℝ),
    (∀ a ∈ s, ProductLeafConstant I N (f a)) →
  ∀ (p : ℝ), 1 ≤ p →
    Real.rpow (∫ x in productBox I, Real.rpow |∑ a ∈ s, f a x| p) (1 / p) ≤
      ∑ a ∈ s, Real.rpow (∫ x in productBox I, Real.rpow |f a x| p) (1 / p)

def rootLpConstMulContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ), ProductLeafConstant I N f →
  ∀ (c p : ℝ), 0 < p →
    Real.rpow (∫ x in productBox I, Real.rpow |c * f x| p) (1 / p) =
      |c| * Real.rpow (∫ x in productBox I, Real.rpow |f x| p) (1 / p)

def rootLpOrderContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f g : ProductPoint d → ℝ),
    ProductLeafConstant I N f → ProductLeafConstant I N g →
    (∀ x ∈ productBox I, |f x| ≤ |g x|) →
  ∀ (p : ℝ), 0 < p →
    Real.rpow (∫ x in productBox I, Real.rpow |f x| p) (1 / p) ≤
      Real.rpow (∫ x in productBox I, Real.rpow |g x| p) (1 / p)

end ReyZygmundVerification
