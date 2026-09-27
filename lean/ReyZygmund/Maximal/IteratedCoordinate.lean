import ReyZygmund.Maximal.CoordinateEstimate

/-!
# A finite list of coordinate maximal functions

List composition preserves the finite product input class and incurs
one ordinary maximal factor per list entry. The list may be empty or repeat a
coordinate. This does not assert domination of a rectangular maximal function.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- Every finite list of coordinate maximal functions preserves the
same constancy on the smallest product cubes, without a dimension or support premise. -/
theorem productLeafConstant_foldr_coordinateDyadicMaximal
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (order : List (Fin m))
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f) :
    ProductLeafConstant I N
      (order.foldr (fun i g => coordinateDyadicMaximal i (I i) (N i) g) f) := by
  induction order with
  | nil => exact hf
  | cons i order ih => exact productLeafConstant_coordinateDyadicMaximal ih i

/-- Iterating the coordinate estimate gives the exact power of the
ordinary maximal constant, with one factor for each occurrence in the list. -/
theorem finite_iterated_coordinate_maximal_integral
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (order : List (Fin m))
    (hd : ∀ i ∈ order, 0 < d i)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (p : ℝ) (hp : 1 < p) :
    (∫ x in productBox I,
      Real.rpow |(order.foldr (fun i g => coordinateDyadicMaximal i (I i) (N i) g) f) x| p) ≤
      Real.rpow (p / (p - 1)) (p * (order.length : ℝ)) *
        (∫ x in productBox I, Real.rpow |f x| p) := by
  have hc : 0 < p / (p - 1) := div_pos (lt_trans zero_lt_one hp) (sub_pos.mpr hp)
  revert hd
  induction order with
  | nil =>
    intro _
    simp
  | cons i order ih =>
    intro hd
    let g : ProductPoint d → ℝ :=
      order.foldr (fun j h => coordinateDyadicMaximal j (I j) (N j) h) f
    have hg : ProductLeafConstant I N g :=
      productLeafConstant_foldr_coordinateDyadicMaximal I N order f hf
    have hstep := finite_coordinate_maximal_integral I N i (hd i List.mem_cons_self)
      g hg p hp
    have htail := ih (fun j hj => hd j (List.mem_cons_of_mem i hj))
    have habs (x : ProductPoint d) :
        |coordinateDyadicMaximal i (I i) (N i) g x| =
          coordinateDyadicMaximal i (I i) (N i) g x :=
      abs_of_nonneg (coordinateDyadicMaximal_nonneg i (I i) (N i) g x)
    have hcoeff : Real.rpow (p / (p - 1)) p *
        Real.rpow (p / (p - 1)) (p * (order.length : ℝ)) =
        Real.rpow (p / (p - 1)) (p * ((i :: order).length : ℝ)) := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hc]
      congr 1
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring
    change (∫ x in productBox I,
      Real.rpow |coordinateDyadicMaximal i (I i) (N i) g x| p) ≤
        Real.rpow (p / (p - 1)) (p * ((i :: order).length : ℝ)) *
          (∫ x in productBox I, Real.rpow |f x| p)
    simp_rw [habs]
    calc
      _ ≤ Real.rpow (p / (p - 1)) p *
          (∫ x in productBox I, Real.rpow |g x| p) := hstep
      _ ≤ Real.rpow (p / (p - 1)) p *
          (Real.rpow (p / (p - 1)) (p * (order.length : ℝ)) *
            (∫ x in productBox I, Real.rpow |f x| p)) :=
        mul_le_mul_of_nonneg_left htail (Real.rpow_nonneg hc.le p)
      _ = _ := by rw [← mul_assoc, hcoeff]

end ReyZygmund
