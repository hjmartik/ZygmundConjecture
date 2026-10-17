import ReyZygmund.Geometry.ProductContainment
import ReyZygmund.Maximal.WeaklyIncomparableFinite

/-! # The maximal-to-square reduction under weak incomparability

The equal-factor condition supplies weak incomparability. The enlarged-family
reduction then applies with the original projection and the same dimension
constant.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- The maximal-to-square reduction in the equal-factor form of weak
incomparability, with the original projection and dimension constant. -/
theorem finite_weaker_maximal_to_square
    (hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : ∀ R ∈ G, ∀ J ∈ G,
      (∀ i, R i ≤ J i) → ∃ i, R i = J i)
    (f : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N f.1)
    (hs : ∀ x, x ∉ productRectangle I → f.1 x = 0)
    (hpos : ∀ x ∈ productRectangle I, 0 ≤ f.1 x)
    (p : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 : ℝ) / 2) :
    let C := (m : ℝ) * (2 : ℝ) ^ m *
      ((2 : ℝ) ^ (6 * (∑ i, d i) + 10) + (2 : ℝ) ^ (m - 1))
    Real.rpow (∫ x in productRectangle I,
      Real.rpow (finiteFamilyMaximal (G ∪ averagingRectangles I N G) f x) p) (1 / p) ≤
      C * (p / (p - 1)) ^ (m - 2) *
        Real.rpow (∫ x in productRectangle I, Real.rpow |f.1 x| p) (1 / p) +
      C * Real.rpow (∫ x in productRectangle I,
        Real.rpow (finiteComplementSquareFunction I N (finiteProjectionMap I N G f) x) p)
        (1 / p) := by
  have hstrict := (weaklyIncomparable_iff_equal_factor
    (G : Set (∀ i, Box (Fin (d i))))).mpr hweak
  exact finite_weakly_incomparable_maximal_to_square hm I N hd G hG hstrict
    f hf hs hpos p hp hp3

end ReyZygmund
