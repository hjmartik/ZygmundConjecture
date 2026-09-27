import ReyZygmund.Geometry.ProductClosure

/-!
# Slice and finite-input properties of the cross-coordinate average

The partition is fixed by the other coordinate indices, not by a spatial
selection. Its slice is precisely the previously constructed one-coordinate
average. In particular it preserves the integral in that coordinate.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

theorem coordinateCrossAverage_slice
    (i : Fin m) (I : Box (Fin (d i))) (N : ℕ)
    (eligible : Finset (Box (Fin (d i)))) (f : ProductPoint d → ℝ)
    (x : ProductPoint d) :
    (fun y => coordinateCrossAverage i I N eligible f (Function.update x i y)) =
      finiteCrossAverage I N eligible (fun y => f (Function.update x i y)) := by
  funext y
  simp [coordinateCrossAverage, Function.update_idem]

/-- The coordinate integral is preserved when the input slice is integrable on the top
cube. Values outside that cube are unrestricted. -/
theorem coordinateCrossAverage_integral
    (i : Fin m) (I : Box (Fin (d i))) (N : ℕ)
    (eligible : Finset (Box (Fin (d i)))) (he : eligible ⊆ descendants I N)
    (f : ProductPoint d → ℝ) (x : ProductPoint d)
    (hf : IntegrableOn (fun y => f (Function.update x i y))
      (I : Set (Fin (d i) → ℝ)) volume) :
    Integrable (fun y => coordinateCrossAverage i I N eligible f (Function.update x i y))
      volume ∧
      (∫ y, coordinateCrossAverage i I N eligible f (Function.update x i y)) =
        ∫ y in (I : Set (Fin (d i) → ℝ)), f (Function.update x i y) := by
  rw [coordinateCrossAverage_slice]
  exact ⟨finiteCrossAverage_integrable I N eligible _, finiteCrossAverage_integral he _ hf⟩

/-- Averaging preserves constancy on the smallest product rectangles and
zero extension outside the top rectangle. -/
theorem coordinateCrossAverage_productStep_closure
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hs : ∀ x, x ∉ productBox I → f x = 0)
    (i : Fin m) (eligible : Finset (Box (Fin (d i))))
    (he : eligible ⊆ descendants (I i) (N i)) :
    ProductLeafConstant I N (coordinateCrossAverage i (I i) (N i) eligible f) ∧
      ∀ x, x ∉ productBox I → coordinateCrossAverage i (I i) (N i) eligible f x = 0 := by
  rw [coordinateCrossAverage_eq_sum]
  constructor
  · apply productLeafConstant_finsetSum
    intro Q hQ
    exact productLeafConstant_coordinateAverage hf i Q
      (partitionCubes_subset_descendants he hQ)
  · intro x hx
    simp only [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro Q hQ
    exact coordinateAverage_eq_zero_of_notMem_productBox hs i Q
      (le_of_mem_descendants (partitionCubes_subset_descendants he hQ)) hx

end ReyZygmund.Geometry
