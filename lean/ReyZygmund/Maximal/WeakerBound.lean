import ReyZygmund.Maximal.WeaklyIncomparableFinite

/-!
# The finite maximal estimate under weaker containment

The equal-factor formulation follows from the weak-incomparability argument
in `WeaklyIncomparableFinite`: the enlarged family has the same projection, its
averages are represented, and the weighted square estimate is absorbed.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- The finite strict-positive union estimate in the paper's weaker-containment
proof. The original projection and `maximalDimensionConstant` are unchanged. -/
theorem finite_weaker_union_maximal_norm
    (hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : ∀ R ∈ G, ∀ J ∈ G,
      (∀ i, R i ≤ J i) → ∃ i, R i = J i)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productBox I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 : ℝ) / 2) :
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal (G ∪ averagingRectangles I N G)
        (finiteInput I N f hf) x) p) (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p) := by
  apply finite_weakly_incomparable_union_maximal_norm hm I N hd G hG ?_
    f hf hfpos p hp hp3
  intro R hR S hS hstrict
  obtain ⟨i, hi⟩ := hweak R hR S hS (fun i => (hstrict i).le)
  exact (ne_of_lt (hstrict i)) hi

/-- The original-family finite bound follows from inclusion into the union,
not from inclusion into the averaging family. -/
theorem finite_weaker_maximal_norm
    (hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : ∀ R ∈ G, ∀ J ∈ G,
      (∀ i, R i ≤ J i) → ∃ i, R i = J i)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productBox I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 : ℝ) / 2) :
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal G (finiteInput I N f hf) x) p) (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p) := by
  apply finite_weakly_incomparable_maximal_norm hm I N hd G hG ?_
    f hf hfpos p hp hp3
  intro R hR S hS hstrict
  obtain ⟨i, hi⟩ := hweak R hR S hS (fun i => (hstrict i).le)
  exact (ne_of_lt (hstrict i)) hi

end ReyZygmund
