import ReyZygmund.Weighted.CrossAverage
import ReyZygmund.Geometry.CrossProperties
import ReyZygmund.Geometry.ProductIntegration

/-! # Integrating a weighted cross-coordinate average

Fix all coordinates except the averaging coordinate and apply the one-coordinate
partition inequality. The functions remain constant on the smallest product cubes,
so the integrals on slices and on the top rectangle are finite. Values outside
that rectangle are unrestricted.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem update_mem_root (I : ∀ i, Box (Fin (d i)))
    {x : ProductPoint d} (hx : x ∈ productBox I) (j : Fin m)
    {y : Fin (d j) → ℝ} (hy : y ∈ I j) :
    Function.update x j y ∈ productBox I := by
  apply (mem_productBox I _).mpr
  intro i
  by_cases hij : i = j
  · subst i
    simpa using hy
  · simpa [hij] using (mem_productBox I x).mp hx i

private theorem root_slice_leaf (I : ∀ i, Box (Fin (d i)))
    (N : Fin m → ℕ) (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (j : Fin m) {x : ProductPoint d} (hx : x ∈ productBox I) :
    ∀ Q ∈ leaves (I j) (N j), ∀ y ∈ Q, ∀ z ∈ Q,
      f (Function.update x j y) = f (Function.update x j z) := by
  intro Q hQ y hy z hz
  have h := productStep_coordinate_leafConstant I N f hf j x Q hQ y hy z hz
  simpa only [Set.indicator_of_mem (update_mem_root I hx j ((level (I j) (N j)).le_of_mem hQ hy)),
    Set.indicator_of_mem (update_mem_root I hx j ((level (I j) (N j)).le_of_mem hQ hz))] using h

private theorem cross_leaf (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (j : Fin m) (eligible : Finset (Box (Fin (d j))))
    (he : eligible ⊆ descendants (I j) (N j)) :
    ProductLeafConstant I N (coordinateCrossAverage j (I j) (N j) eligible f) := by
  rw [coordinateCrossAverage_eq_sum]
  apply productLeafConstant_finsetSum
  intro Q hQ
  exact productLeafConstant_coordinateAverage hf j Q
    (partitionCubes_subset_descendants he hQ)

/-- Positivity is preserved on the top rectangle, with no assumption outside it. -/
theorem coordinateCrossAverage_pos_on_root
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (v : ProductPoint d → ℝ) (hv : ProductLeafConstant I N v)
    (hvpos : ∀ x ∈ productBox I, 0 < v x)
    (j : Fin m) (eligible : Finset (Box (Fin (d j))))
    (he : eligible ⊆ descendants (I j) (N j))
    (x : ProductPoint d) (hx : x ∈ productBox I) :
    0 < coordinateCrossAverage j (I j) (N j) eligible v x := by
  exact finiteCrossAverage_pos (I j) (N j) eligible he
    (fun y => v (Function.update x j y)) (root_slice_leaf I N v hv j hx)
    (fun y hy => hvpos _ (update_mem_root I hx j hy)) (x j)
    ((mem_productBox I x).mp hx j)

/-- Weighted cross-coordinate contraction for a signed numerator and a weight positive
on the top rectangle, including `p = 2`. -/
theorem coordinateCrossAverage_weighted_square_integral
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (u v : ProductPoint d → ℝ) (hu : ProductLeafConstant I N u)
    (hv : ProductLeafConstant I N v) (hvpos : ∀ x ∈ productBox I, 0 < v x)
    (j : Fin m) (eligible : Finset (Box (Fin (d j))))
    (he : eligible ⊆ descendants (I j) (N j))
    (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
    (∫ x in productBox I,
        (coordinateCrossAverage j (I j) (N j) eligible u x) ^ 2 /
          Real.rpow (coordinateCrossAverage j (I j) (N j) eligible v x) (2 - p)) ≤
      ∫ x in productBox I, (u x) ^ 2 / Real.rpow (v x) (2 - p) := by
  have hXu := cross_leaf I N u hu j eligible he
  have hXv := cross_leaf I N v hv j eligible he
  have hH : ProductLeafConstant I N
      (fun x => (coordinateCrossAverage j (I j) (N j) eligible u x) ^ 2 /
        Real.rpow (coordinateCrossAverage j (I j) (N j) eligible v x) (2 - p)) := by
    intro Q hQ x hx y hy
    dsimp only
    rw [hXu Q hQ x hx y hy, hXv Q hQ x hx y hy]
  have hK : ProductLeafConstant I N (fun x => (u x) ^ 2 / Real.rpow (v x) (2 - p)) := by
    intro Q hQ x hx y hy
    dsimp only
    rw [hu Q hQ x hx y hy, hv Q hQ x hx y hy]
  have h := integral_product_le_of_coordinate_le I N _ _ hH hK
    (fun x hx => div_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (coordinateCrossAverage_pos_on_root I N v hv hvpos j eligible he x hx).le _))
    (fun x hx => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (hvpos x hx).le _))
    1 zero_le_one j (by
      intro x hx
      have hslice := finiteCrossAverage_weighted_square_integral (I j) (N j) eligible he
        (fun y => u (Function.update x j y)) (fun y => v (Function.update x j y))
        (root_slice_leaf I N u hu j hx) (root_slice_leaf I N v hv j hx)
        (fun y hy => hvpos _ (update_mem_root I hx j hy)) p hp hp2
      simp only [one_mul]
      simpa only [coordinateCrossAverage, Function.update_self, Function.update_idem] using hslice)
  simpa only [one_mul] using h

end ReyZygmund
