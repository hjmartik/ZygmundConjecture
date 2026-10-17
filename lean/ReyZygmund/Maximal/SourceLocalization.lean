import ReyZygmund.Maximal.Forest
import ReyZygmund.Geometry.ProductContainment

/-! # Localizing the input for the whole-grid estimate

Restricting the input to a top rectangle preserves averages over all family
members contained there. Thus the localization identities apply to these
restricted inputs.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- Localization preserves every selected mean because the restricted integrands agree. -/
theorem finiteFunctionMaximal_indicator_root
    (H : Finset (∀ i, Box (Fin (d i)))) (R : ∀ i, Box (Fin (d i)))
    (hH : ∀ Q ∈ H, productRectangle Q ⊆ productRectangle R)
    (f : ProductPoint d → ℝ) :
    finiteFunctionMaximal H ((productRectangle R).indicator f) =
      finiteFunctionMaximal H f := by
  funext x
  by_cases hne : H.Nonempty
  · simp only [finiteFunctionMaximal, dite_eq_left hne]
    apply Finset.sup'_congr hne rfl
    intro Q hQ
    have hi : (∫ y in productRectangle Q, |((productRectangle R).indicator f) y|) =
        ∫ y in productRectangle Q, |f y| := by
      apply setIntegral_congr_fun (measurableSet_productRectangle Q)
      intro y hy
      change |(productRectangle R).indicator f y| = |f y|
      rw [Set.indicator_of_mem (hH Q hQ hy)]
    rw [hi]
  · simp only [finiteFunctionMaximal, dite_eq_right hne]

/-- Pointwise localization to disjoint top rectangles, with the input restricted
to each top rectangle. -/
theorem source_finite_maximal_localization
    (T G : Finset (∀ i, Box (Fin (d i))))
    (hdis : Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (productRectangle R) (productRectangle S)))
    (hcover : ∀ Q ∈ G, ∃ R ∈ T, ∀ i, Q i ≤ R i)
    (f : ProductPoint d → ℝ) (x : ProductPoint d) :
    finiteFunctionMaximal G f x =
      ∑ R ∈ T, finiteFunctionMaximal
        (G.filter (fun Q => ∀ i, Q i ≤ R i)) ((productRectangle R).indicator f) x := by
  rw [finiteFunctionMaximal_forest T G hdis hcover f x]
  apply Finset.sum_congr rfl
  intro R _hR
  rw [finiteFunctionMaximal_indicator_root _ R
    (fun Q hQ => (productRectangle_subset_iff Q R).mpr (Finset.mem_filter.mp hQ).2)]

/-- The corresponding power-integral localization identity. -/
theorem source_finite_maximal_integral_localization
    (T G : Finset (∀ i, Box (Fin (d i))))
    (hdis : Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (productRectangle R) (productRectangle S)))
    (hcover : ∀ Q ∈ G, ∃ R ∈ T, ∀ i, Q i ≤ R i)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 0 < p) :
    (∫ x, Real.rpow (finiteFunctionMaximal G f x) p) =
      ∑ R ∈ T, ∫ x,
        Real.rpow (finiteFunctionMaximal
          (G.filter (fun Q => ∀ i, Q i ≤ R i)) ((productRectangle R).indicator f) x) p := by
  rw [integral_rpow_finiteFunctionMaximal_forest T G hdis hcover f p hp]
  apply Finset.sum_congr rfl
  intro R _hR
  rw [finiteFunctionMaximal_indicator_root _ R
    (fun Q hQ => (productRectangle_subset_iff Q R).mpr (Finset.mem_filter.mp hQ).2)]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : finiteFunctionMaximal (G.filter (fun Q => ∀ i, Q i ≤ R i)) f x = 0 := by
    apply finiteFunctionMaximal_eq_zero_of_outside
    intro Q hQ hxQ
    exact hx ((productRectangle_subset_iff Q R).mpr (Finset.mem_filter.mp hQ).2 hxQ)
  simp only [hz, Real.rpow_eq_pow, Real.zero_rpow hp.ne']

end ReyZygmund
