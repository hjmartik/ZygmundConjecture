import ReyZygmund.Maximal.FiniteOrdinary
import ReyZygmund.Geometry.ProductClosure

/-! # The finite dyadic maximal function in one coordinate

Hold the other coordinates fixed and take the maximal function in the selected
coordinate. Its averages include the top cube and the smallest cubes in the finite
grid.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- Apply the finite dyadic maximal function to one coordinate slice. -/
noncomputable def coordinateDyadicMaximal (i : Fin m) (I : Box (Fin (d i)))
    (N : ℕ) (f : ProductPoint d → ℝ) (x : ProductPoint d) : ℝ :=
  finiteDyadicMaximal I N (fun y => f (Function.update x i y)) (x i)

/-- The slice maximum is the finite maximum of coordinate level averages. -/
theorem coordinateDyadicMaximal_eq_level_sup (i : Fin m) (I : Box (Fin (d i)))
    (N : ℕ) (f : ProductPoint d → ℝ) (x : ProductPoint d) :
    coordinateDyadicMaximal i I N f x =
      (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        (fun n => ∑ Q ∈ (level I n).boxes,
          coordinateAverage i Q (fun y => |f y|) x) := rfl

theorem coordinateDyadicMaximal_nonneg (i : Fin m) (I : Box (Fin (d i)))
    (N : ℕ) (f : ProductPoint d → ℝ) (x : ProductPoint d) :
    0 ≤ coordinateDyadicMaximal i I N f x :=
  finiteDyadicMaximal_nonneg I N (fun y => f (Function.update x i y)) (x i)

/-- Measurability is joint in all coordinates and needs no integrability premise. -/
theorem measurable_coordinateDyadicMaximal (i : Fin m) (I : Box (Fin (d i)))
    (N : ℕ) (f : ProductPoint d → ℝ) (hf : Measurable f) :
    Measurable (coordinateDyadicMaximal i I N f) := by
  change Measurable (fun x =>
    (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      (fun n => ∑ Q ∈ (level I n).boxes,
        coordinateAverage i Q (fun y => |f y|) x))
  apply Finset.measurable_range_sup''
  intro n _
  exact Finset.measurable_sum _
    (fun Q _ => coordinateAverage_measurable i Q (fun y => |f y|)
      (by simpa only [Real.norm_eq_abs] using hf.norm))

/-- The coordinate maximal function preserves constancy on the smallest product cubes, with no restrictions outside the top rectangle. -/
theorem productLeafConstant_coordinateDyadicMaximal
    {I : ∀ i, Box (Fin (d i))} {N : Fin m → ℕ} {f : ProductPoint d → ℝ}
    (hf : ProductLeafConstant I N f) (i : Fin m) :
    ProductLeafConstant I N (coordinateDyadicMaximal i (I i) (N i) f) := by
  have habs : ProductLeafConstant I N (fun x => |f x|) := by
    intro P hP x hx y hy
    exact congrArg abs (hf P hP x hx y hy)
  intro P hP x hx y hy
  rw [coordinateDyadicMaximal_eq_level_sup, coordinateDyadicMaximal_eq_level_sup]
  apply Finset.sup'_congr Finset.nonempty_range_add_one rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro Q hQ
  exact productLeafConstant_coordinateAverage habs i Q
    (mem_descendants.mpr
      ⟨n, Nat.lt_succ_iff.mp (Finset.mem_range.mp hn), hQ⟩) P hP x hx y hy

/-- Support in the top rectangle is preserved pointwise, independently of constancy on small cubes. -/
theorem coordinateDyadicMaximal_eq_zero_of_notMem_productBox
    {I : ∀ i, Box (Fin (d i))} {N : Fin m → ℕ} {f : ProductPoint d → ℝ}
    (hs : ∀ x, x ∉ productBox I → f x = 0) (i : Fin m)
    {x : ProductPoint d} (hx : x ∉ productBox I) :
    coordinateDyadicMaximal i (I i) (N i) f x = 0 := by
  rw [coordinateDyadicMaximal_eq_level_sup]
  apply Finset.sup'_eq_of_forall
  intro n _
  apply Finset.sum_eq_zero
  intro Q hQ
  exact coordinateAverage_eq_zero_of_notMem_productBox
    (fun y hy => by rw [hs y hy, abs_zero]) i Q ((level (I i) n).le_of_mem hQ) hx

/-- Updating the averaged coordinate leaves precisely the same slice. -/
theorem coordinateDyadicMaximal_update (i : Fin m) (I : Box (Fin (d i)))
    (N : ℕ) (f : ProductPoint d → ℝ) (x : ProductPoint d) (y : Fin (d i) → ℝ) :
    coordinateDyadicMaximal i I N f (Function.update x i y) =
      finiteDyadicMaximal I N (fun z => f (Function.update x i z)) y := by
  simp only [coordinateDyadicMaximal, Function.update_self, Function.update_idem]

end ReyZygmund
