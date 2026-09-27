import ReyZygmund.Geometry.ProductMaps

/-! # Coordinate operators on finite step functions

Averages over retained descendants preserve constancy on the smallest product
cubes. Interior differences also preserve it, since their children lie at or above
the smallest retained scale. Support in the top rectangle is preserved pointwise.
These properties justify iteration of the operators.


-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}
variable {I : ∀ i, Box (Fin (d i))} {N : Fin m → ℕ} {f : ProductPoint d → ℝ}

theorem productLeafConstant_indicator (hf : ProductLeafConstant I N f) :
    ProductLeafConstant I N ((productBox I).indicator f) := by
  intro P hP x hx y hy
  rw [Set.indicator_of_mem (productLeaves_subset hP hx),
    Set.indicator_of_mem (productLeaves_subset hP hy)]
  exact hf P hP x hx y hy

theorem productLeafConstant_sub {g : ProductPoint d → ℝ}
    (hf : ProductLeafConstant I N f) (hg : ProductLeafConstant I N g) :
    ProductLeafConstant I N (f - g) := by
  intro P hP x hx y hy
  change f x - g x = f y - g y
  rw [hf P hP x hx y hy, hg P hP x hx y hy]

theorem productLeafConstant_finsetSum {κ : Type*} (s : Finset κ)
    (g : κ → ProductPoint d → ℝ) (hg : ∀ k ∈ s, ProductLeafConstant I N (g k)) :
    ProductLeafConstant I N (∑ k ∈ s, g k) := by
  intro P hP x hx y hy
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun k hk => hg k hk P hP x hx y hy)

namespace ProductClosure

/-- Replacing one coordinate by a common point of its top cube preserves equality of
values on a smallest product cube. -/
theorem update_eq (hf : ProductLeafConstant I N f)
    {P : ∀ i, Box (Fin (d i))} (hP : P ∈ productLeaves I N)
    {x y : ProductPoint d} (hx : x ∈ productBox P) (hy : y ∈ productBox P)
    (i : Fin m) {z : Fin (d i) → ℝ} (hz : z ∈ I i) :
    f (Function.update x i z) = f (Function.update y i z) := by
  obtain ⟨R, hR, hzR⟩ := level_isPartition (I i) (N i) z hz
  have hPR : Function.update P i R ∈ productLeaves I N := by
    apply Fintype.mem_piFinset.mpr
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hR
    · simpa [hji] using Fintype.mem_piFinset.mp hP j
  have hmem : ∀ w ∈ productBox P,
      Function.update w i z ∈ productBox (Function.update P i R) := by
    intro w hw
    apply (mem_productBox _ _).mpr
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hzR
    · simpa [hji] using (mem_productBox P w).mp hw j
  exact hf _ hPR _ (hmem x hx) _ (hmem y hy)

end ProductClosure

/-- Averages may use every descendant, including the smallest cubes. -/
theorem productLeafConstant_coordinateAverage (hf : ProductLeafConstant I N f)
    (i : Fin m) (Q : Box (Fin (d i))) (hQ : Q ∈ descendants (I i) (N i)) :
    ProductLeafConstant I N (coordinateAverage i Q f) := by
  obtain ⟨n, hn, hQn⟩ := mem_descendants.mp hQ
  intro P hP x hx y hy
  have hxP := (mem_productBox P x).mp hx i
  have hyP := (mem_productBox P y).mp hy i
  rcases level_le_or_disjoint hn (Fintype.mem_piFinset.mp hP i) hQn with hPQ | hdis
  · rw [coordinateAverage_of_mem i Q f x (hPQ hxP),
      coordinateAverage_of_mem i Q f y (hPQ hyP)]
    congr 1
    exact setIntegral_congr_fun Q.measurableSet_coe (fun z hz =>
      ProductClosure.update_eq hf hP hx hy i ((level (I i) n).le_of_mem hQn hz))
  · rw [coordinateAverage_of_notMem i Q f x
      (fun hxQ => Set.disjoint_left.mp hdis hxP hxQ),
      coordinateAverage_of_notMem i Q f y
        (fun hyQ => Set.disjoint_left.mp hdis hyP hyQ)]

/-- Support follows from containment in the top rectangle, without constancy or positivity assumptions. -/
theorem coordinateAverage_eq_zero_of_notMem_productBox
    (hs : ∀ x, x ∉ productBox I → f x = 0)
    (i : Fin m) (Q : Box (Fin (d i))) (hQI : Q ≤ I i)
    {x : ProductPoint d} (hx : x ∉ productBox I) : coordinateAverage i Q f x = 0 := by
  by_cases hxQ : x i ∈ Q
  · have hzero : ∀ z, f (Function.update x i z) = 0 := by
      intro z
      apply hs
      intro hzx
      apply hx
      apply (mem_productBox I x).mpr
      intro j
      by_cases hji : j = i
      · subst j
        exact hQI hxQ
      · simpa [hji] using (mem_productBox I _).mp hzx j
    rw [coordinateAverage_of_mem i Q f x hxQ]
    simp [hzero]
  · exact coordinateAverage_of_notMem i Q f x hxQ

namespace ProductClosure

/-- The children of an interior index remain in the finite tree. -/
theorem child_mem_descendants {ι : Type*} [Fintype ι] {B Q R : Box ι} {K : ℕ}
    (hQ : Q ∈ interior B K) (hR : R ∈ Prepartition.splitCenter Q) :
    R ∈ descendants B K := by
  obtain ⟨n, hn, hQn⟩ := mem_interior.mp hQ
  exact mem_descendants.mpr ⟨n + 1, Nat.succ_le_of_lt hn,
    (level B n).mem_biUnion.mpr ⟨Q, hQn, hR⟩⟩

end ProductClosure

/-- Interior indices have all their children at or above the cutoff. -/
theorem productLeafConstant_coordinateDifference (hf : ProductLeafConstant I N f)
    (i : Fin m) (Q : Box (Fin (d i))) (hQ : Q ∈ interior (I i) (N i)) :
    ProductLeafConstant I N (coordinateDifference i Q f) := by
  unfold coordinateDifference
  apply productLeafConstant_sub
  · apply productLeafConstant_finsetSum
    intro R hR
    exact productLeafConstant_coordinateAverage hf i R
      (ProductClosure.child_mem_descendants hQ hR)
  · exact productLeafConstant_coordinateAverage hf i Q
      (interior_subset_descendants (I i) (N i) hQ)

theorem coordinateDifference_eq_zero_of_notMem_productBox
    (hs : ∀ x, x ∉ productBox I → f x = 0)
    (i : Fin m) (Q : Box (Fin (d i))) (hQI : Q ≤ I i)
    {x : ProductPoint d} (hx : x ∉ productBox I) : coordinateDifference i Q f x = 0 := by
  simp only [coordinateDifference, Pi.sub_apply, Finset.sum_apply]
  rw [coordinateAverage_eq_zero_of_notMem_productBox hs i Q hQI hx, sub_zero]
  apply Finset.sum_eq_zero
  intro R hR
  exact coordinateAverage_eq_zero_of_notMem_productBox hs i R
    (((Prepartition.splitCenter Q).le_of_mem hR).trans hQI) hx

/-- Coordinate averaging preserves the zero-extended finite input class. -/
theorem coordinateAverage_productStep_closure
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (i : Fin m) (Q : Box (Fin (d i))) (hQ : Q ∈ descendants (I i) (N i)) :
    ProductLeafConstant I N (coordinateAverage i Q ((productBox I).indicator f)) ∧
      ∀ x, x ∉ productBox I → coordinateAverage i Q ((productBox I).indicator f) x = 0 := by
  refine ⟨productLeafConstant_coordinateAverage (productLeafConstant_indicator hf) i Q hQ, ?_⟩
  intro x hx
  exact coordinateAverage_eq_zero_of_notMem_productBox
    (fun y hy => Set.indicator_of_notMem hy f) i Q (le_of_mem_descendants hQ) hx

/-- Coordinate differences preserve the finite input class for interior indices.
No positivity or dimension assumption is needed for this closure statement. -/
theorem coordinateDifference_productStep_closure
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (i : Fin m) (Q : Box (Fin (d i))) (hQ : Q ∈ interior (I i) (N i)) :
    ProductLeafConstant I N (coordinateDifference i Q ((productBox I).indicator f)) ∧
      ∀ x, x ∉ productBox I → coordinateDifference i Q ((productBox I).indicator f) x = 0 := by
  refine ⟨productLeafConstant_coordinateDifference (productLeafConstant_indicator hf) i Q hQ, ?_⟩
  intro x hx
  exact coordinateDifference_eq_zero_of_notMem_productBox
    (fun y hy => Set.indicator_of_notMem hy f) i Q
      (le_of_mem_descendants (interior_subset_descendants (I i) (N i) hQ)) hx

/-- The existing average map retains both properties needed for another iteration. -/
theorem averageMap_productStep_closure
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (i : Fin m) (Q : Box (Fin (d i))) (hQ : Q ∈ descendants (I i) (N i)) :
    ProductLeafConstant I N (averageMap i Q F).1 ∧
      ∀ x, x ∉ productBox I → (averageMap i Q F).1 x = 0 := by
  simpa only [averageMap_apply] using
    And.intro (productLeafConstant_coordinateAverage hf i Q hQ)
      (fun x hx => coordinateAverage_eq_zero_of_notMem_productBox hs i Q
        (le_of_mem_descendants hQ) (x := x) hx)

/-- The existing difference map retains both properties for every interior index. -/
theorem differenceMap_productStep_closure
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (i : Fin m) (Q : Box (Fin (d i))) (hQ : Q ∈ interior (I i) (N i)) :
    ProductLeafConstant I N (differenceMap i Q F).1 ∧
      ∀ x, x ∉ productBox I → (differenceMap i Q F).1 x = 0 := by
  simpa only [differenceMap_apply] using
    And.intro (productLeafConstant_coordinateDifference hf i Q hQ)
      (fun x hx => coordinateDifference_eq_zero_of_notMem_productBox hs i Q
        (le_of_mem_descendants (interior_subset_descendants (I i) (N i) hQ)) (x := x) hx)

/-- Iterating the difference maps preserves the finite source class.
The empty coordinate product acts as the identity, with no exceptional case. -/
theorem productDifferenceMap_productStep_closure
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (A : Finset (Fin m)) (Q : ∀ i, Box (Fin (d i)))
    (hQ : ∀ i ∈ A, Q i ∈ interior (I i) (N i)) :
    ProductLeafConstant I N (productDifferenceMap A Q F).1 ∧
      ∀ x, x ∉ productBox I → (productDifferenceMap A Q F).1 x = 0 := by
  revert hQ
  induction A using Finset.induction_on with
  | empty =>
    intro _
    simpa only [productDifferenceMap_empty, Module.End.one_apply] using And.intro hf hs
  | @insert i A hi ih =>
    intro hQ
    have hA := ih (fun j hj => hQ j (Finset.mem_insert_of_mem hj))
    have hc := differenceMap_productStep_closure I N (productDifferenceMap A Q F)
      hA.1 hA.2 i (Q i) (hQ i (Finset.mem_insert_self i A))
    simpa only [productDifferenceMap_insert A i hi Q, Module.End.mul_apply] using hc

end ReyZygmund.Geometry
