import ReyZygmund.Geometry.ProductClosure

/-! # Constancy and positivity of product averages

Compositions of coordinate averages preserve constancy on the smallest cubes. For
input strictly positive on the top rectangle, the output is positive where the
selected coordinates lie in their averaging cubes and the other coordinates lie in
the top cubes. This is the support region used in the weighted estimates.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- Iterated averages preserve constancy on the smallest cubes and support in the top rectangle, pointwise. -/
theorem productAverageMap_productStep_closure
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (A : Finset (Fin m)) (Q : ∀ i, Box (Fin (d i)))
    (hQ : ∀ i ∈ A, Q i ∈ descendants (I i) (N i)) :
    ProductLeafConstant I N (productAverageMap A Q F).1 ∧
      ∀ x, x ∉ productBox I → (productAverageMap A Q F).1 x = 0 := by
  revert hQ
  induction A using Finset.induction_on with
  | empty =>
    intro _
    simpa only [productAverageMap_empty, Module.End.one_apply] using And.intro hf hs
  | @insert i A hi ih =>
    intro hQ
    have hA := ih (fun j hj => hQ j (Finset.mem_insert_of_mem hj))
    have hc := averageMap_productStep_closure I N (productAverageMap A Q F)
      hA.1 hA.2 i (Q i) (hQ i (Finset.mem_insert_self i A))
    simpa only [productAverageMap_insert A i hi Q, Module.End.mul_apply] using hc

/-- Positivity of an average on its positive, integrable slice. -/
theorem coordinateAverage_pos (F : boundedMeasurableFunctions d)
    (i : Fin m) (Q : Box (Fin (d i))) (x : ProductPoint d) (hx : x i ∈ Q)
    (hpos : ∀ y ∈ Q, 0 < F.1 (Function.update x i y)) :
    0 < coordinateAverage i Q F.1 x := by
  obtain ⟨C, _, hC⟩ := F.2.2
  have hfi := integrable_coordinateSlice F.1 F.2.1 C hC i Q x
  have hnonneg : 0 ≤ᵐ[volume.restrict (Q : Set (Fin (d i) → ℝ))]
      (fun y => F.1 (Function.update x i y)) := by
    filter_upwards [self_mem_ae_restrict Q.measurableSet_coe] with y hy
    exact (hpos y hy).le
  have hsupp : Function.support (fun y => F.1 (Function.update x i y)) ∩
      (Q : Set (Fin (d i) → ℝ)) = (Q : Set (Fin (d i) → ℝ)) := by
    apply Set.inter_eq_right.mpr
    intro y hy
    exact ne_of_gt (hpos y hy)
  rw [coordinateAverage_of_mem i Q F.1 x hx]
  apply div_pos _ (box_volume_pos Q)
  apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hfi).mpr
  rw [hsupp, ← ofReal_measureReal (Q.measure_coe_lt_top volume).ne]
  exact ENNReal.ofReal_pos.mpr (box_volume_pos Q)

/-- Strict positivity holds where selected coordinates lie in their averaging cubes and
unselected coordinates lie in top cubes. Constancy on the smallest cubes is not needed. -/
theorem productAverageMap_pos
    (I : ∀ i, Box (Fin (d i))) (F : boundedMeasurableFunctions d)
    (hpos : ∀ x ∈ productBox I, 0 < F.1 x)
    (A : Finset (Fin m)) (Q : ∀ i, Box (Fin (d i)))
    (hQ : ∀ i ∈ A, Q i ≤ I i)
    (x : ProductPoint d) (hx : x ∈ productBox I) (hxQ : ∀ i ∈ A, x i ∈ Q i) :
    0 < (productAverageMap A Q F).1 x := by
  revert hQ x
  induction A using Finset.induction_on with
  | empty =>
    intro _ x hx _
    simpa only [productAverageMap_empty, Module.End.one_apply] using hpos x hx
  | @insert i A hi ih =>
    intro hQ x hx hxQ
    rw [productAverageMap_insert A i hi Q, Module.End.mul_apply, averageMap_apply]
    apply coordinateAverage_pos (productAverageMap A Q F) i (Q i) x
      (hxQ i (Finset.mem_insert_self i A))
    intro y hy
    refine ih (fun j hj => hQ j (Finset.mem_insert_of_mem hj))
      (Function.update x i y) ?_ ?_
    · apply (mem_productBox I _).mpr
      intro j
      by_cases hji : j = i
      · subst j
        simpa using (hQ i (Finset.mem_insert_self i A)) hy
      · simpa [hji] using (mem_productBox I x).mp hx j
    · intro j hj
      have hji : j ≠ i := by
        intro h
        subst j
        exact hi hj
      simpa [hji] using hxQ j (Finset.mem_insert_of_mem hj)

end ReyZygmund.Geometry
