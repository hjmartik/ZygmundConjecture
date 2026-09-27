import ReyZygmund.Geometry.ProductClosure
import ReyZygmund.Geometry.FiniteDifferenceAlgebra

/-! # Differences at and below the smallest retained scale

Constancy on a smallest cube makes its child-minus-parent difference vanish, as
well as the differences on smaller cubes. The definition of a difference is
unchanged at that scale. -/

open BoxIntegral MeasureTheory
open scoped Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

theorem productLeafConstant_coordinate_slice
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hs : ∀ x, x ∉ productBox I → f x = 0)
    (i : Fin m) (P : Box (Fin (d i))) (hP : P ∈ level (I i) (N i))
    (x : ProductPoint d) :
    ∀ y ∈ P, ∀ z ∈ P, f (Function.update x i y) = f (Function.update x i z) := by
  have hi : (productBox I).indicator f = f := Set.indicator_eq_self.mpr (by
    intro x hx
    by_contra hout
    exact hx (hs x hout))
  simpa only [hi] using productStep_coordinate_leafConstant I N f hf i x P hP

/-- The cancellation includes the smallest cube itself and every cube below it,
whether or not that cube is in the selected finite family. -/
theorem coordinateDifference_eq_zero_below_leaf
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hs : ∀ x, x ∉ productBox I → f x = 0)
    (i : Fin m) (P Q : Box (Fin (d i))) (hP : P ∈ level (I i) (N i))
    (hQP : Q ≤ P) : coordinateDifference i Q f = 0 := by
  funext x
  rw [coordinateDifference_slice]
  have hconst : ∀ y ∈ Q, ∀ z ∈ Q,
      f (Function.update x i y) = f (Function.update x i z) := by
    intro y hy z hz
    exact productLeafConstant_coordinate_slice I N f hf hs i P hP x
      y (hQP hy) z (hQP hz)
  exact congrFun (DifferenceAlgebra.boxDifference_of_constant Q _ hconst) (x i)

end ReyZygmund.Geometry
