import ReyZygmund.Geometry.ProductContainment
import ReyZygmund.Maximal.WeaklyIncomparableFinite

/-! # Representation under weak incomparability

The equal-factor condition says that a containment between two family members
leaves at least one coordinate factor unchanged. It gives weak incomparability,
so the representation and maximal estimate on the enlarged family apply.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- The signed representation in the equal-factor form of weak incomparability.
The projection is defined from the original family. -/
theorem Projection.finite_weaker_representation
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : ∀ R ∈ G, ∀ J ∈ G,
      (∀ i, R i ≤ J i) → ∃ i, R i = J i)
    (R : ∀ i, Box (Fin (d i)))
    (hR : R ∈ G ∪ averagingRectangles I N G)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productRectangle I → F.1 x = 0)
    (x : ProductPoint d) (hx : x ∈ productRectangle R) :
    (productAverageMap Finset.univ R F).1 x =
      ∑ A ∈ ((Finset.univ : Finset (Fin m)).powerset.erase Finset.univ),
        (-1 : ℝ) ^ (m + 1 + A.card) *
          (productAverageMap A R (finiteProjectionMap I N G F)).1 x := by
  have hstrict := (weaklyIncomparable_iff_equal_factor
    (G : Set (∀ i, Box (Fin (d i))))).mpr hweak
  exact finite_weakly_incomparable_representation I N hd G hG hstrict R hR F hf hs x hx

/-- The union maximal function has the same pointwise `2^m` bound. Taking a
finite supremum does not add the separate original and averaging bounds. -/
theorem finite_weaker_representation_maximal
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : ∀ R ∈ G, ∀ J ∈ G,
      (∀ i, R i ≤ J i) → ∃ i, R i = J i)
    (f : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N f.1)
    (hs : ∀ x, x ∉ productRectangle I → f.1 x = 0)
    (hpos : ∀ x ∈ productRectangle I, 0 ≤ f.1 x)
    (x : ProductPoint d) (_hx : x ∈ productRectangle I) :
    finiteFamilyMaximal (G ∪ averagingRectangles I N G) f x ≤
      (2 : ℝ) ^ m * ∑ j,
        finiteSignedPartialMaximal I N (Finset.univ.erase j)
          (finiteProjectionMap I N G f) x := by
  have hstrict := (weaklyIncomparable_iff_equal_factor
    (G : Set (∀ i, Box (Fin (d i))))).mpr hweak
  exact finite_weakly_incomparable_representation_maximal I N hd G hG hstrict f hf hs hpos x

end ReyZygmund
