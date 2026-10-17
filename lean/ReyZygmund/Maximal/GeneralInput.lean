import ReyZygmund.Geometry.LeafAverages
import ReyZygmund.Maximal.Family

/-! # Finite maximal functions and input averaging

The finite maximum uses normalized integrals of `|f|`. Averaging `|f|` on the
smallest cubes preserves every selected average. This reduces integrable inputs
to bounded functions that are constant on the smallest cubes.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- The finite maximum of supported normalized integrals of `|f|`. -/
noncomputable def finiteFunctionMaximal
    (G : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ)
    (x : ProductPoint d) : ℝ :=
  if h : G.Nonempty then G.sup' h (fun Q =>
    (productRectangle Q).indicator
      (fun _ => (∫ y in productRectangle Q, |f y|) / volume.real (productRectangle Q)) x)
  else 0

theorem finiteFunctionMaximal_of_bounded
    (G : Finset (∀ i, Box (Fin (d i)))) (F : boundedMeasurableFunctions d) :
    finiteFunctionMaximal G F.1 = finiteFamilyMaximal G F := rfl

/-- Averaging `|f|` on the smallest cubes preserves its averages over all selected
rectangles. -/
theorem finiteFunctionMaximal_leafAverage
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (f : ProductPoint d → ℝ) (hf : IntegrableOn f (productRectangle I) volume) :
    finiteFunctionMaximal G f = finiteFamilyMaximal G
      (finiteInput I N (leafAverage I N (fun x => |f x|))
        (productLeafConstant_leafAverage I N (fun x => |f x|))) := by
  let g := leafAverage I N (fun x => |f x|)
  have hg : ProductLeafConstant I N g := productLeafConstant_leafAverage I N _
  have hnonneg : ∀ x, 0 ≤ g x :=
    leafAverage_nonneg I N (fun x => |f x|) (fun x _ => abs_nonneg (f x))
  have heq : ∀ Q ∈ G,
      (∫ y in productRectangle Q, |(finiteInput I N g hg).1 y|) =
        ∫ y in productRectangle Q, |f y| := by
    intro Q hQ
    calc
      _ = ∫ y in productRectangle Q, g y := by
        apply setIntegral_congr_fun (measurableSet_productRectangle Q)
        intro y hy
        change |(productRectangle I).indicator g y| = g y
        rw [Set.indicator_of_mem (productRectangle_subset_root_of_mem_productDescendants
          (hG hQ) hy), abs_of_nonneg (hnonneg y)]
      _ = _ := integral_leafAverage_descendant I N Q (hG hQ) _ hf.abs
  funext x
  by_cases h : G.Nonempty
  · rw [finiteFunctionMaximal, dite_eq_left h, finiteFamilyMaximal, dite_eq_left h]
    apply Finset.sup'_congr _ rfl
    intro Q hQ
    rw [heq Q hQ]
  · simp only [finiteFunctionMaximal, finiteFamilyMaximal, dite_eq_right h]

end ReyZygmund
