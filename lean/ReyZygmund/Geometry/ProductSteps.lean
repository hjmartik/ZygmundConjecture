import ReyZygmund.Geometry.ProductOperators
import Mathlib.Data.Fintype.Pi

/-!
# Finite product step functions

After restriction to the top rectangle and zero extension, a function constant on
the smallest product cubes has a finite-indicator representation. This gives
measurability, boundedness and slice integrability. Coordinate cutoffs may differ.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- A product rectangle with the prescribed Euclidean coordinate dimensions. -/
def productBox (Q : ∀ i, Box (Fin (d i))) : Set (ProductPoint d) :=
  Set.pi Set.univ (fun i => (Q i : Set (Fin (d i) → ℝ)))

@[simp] theorem mem_productBox (Q : ∀ i, Box (Fin (d i))) (x : ProductPoint d) :
    x ∈ productBox Q ↔ ∀ i, x i ∈ Q i := by
  simp [productBox]

theorem measurableSet_productBox (Q : ∀ i, Box (Fin (d i))) :
    MeasurableSet (productBox Q) :=
  MeasurableSet.univ_pi (fun i => (Q i).measurableSet_coe)

/-- Independent finite cutoffs in the coordinate trees. -/
noncomputable def productLeaves (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) :
    Finset (∀ i, Box (Fin (d i))) :=
  Fintype.piFinset (fun i => leaves (I i) (N i))

theorem productLeaves_cover (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (x : ProductPoint d) (hx : x ∈ productBox I) :
    ∃ Q ∈ productLeaves I N, x ∈ productBox Q := by
  have hi (i : Fin m) := level_isPartition (I i) (N i) (x i) ((mem_productBox I x).mp hx i)
  choose Q hQ hxQ using hi
  exact ⟨Q, Fintype.mem_piFinset.mpr hQ, (mem_productBox Q x).mpr hxQ⟩

theorem productLeaves_subset {I : ∀ i, Box (Fin (d i))} {N : Fin m → ℕ}
    {Q : ∀ i, Box (Fin (d i))} (hQ : Q ∈ productLeaves I N) :
    productBox Q ⊆ productBox I := by
  intro x hx
  apply (mem_productBox I x).mpr
  intro i
  exact (level (I i) (N i)).le_of_mem (Fintype.mem_piFinset.mp hQ i)
    ((mem_productBox Q x).mp hx i)

theorem productLeaves_unique {I : ∀ i, Box (Fin (d i))} {N : Fin m → ℕ}
    {Q R : ∀ i, Box (Fin (d i))} (hQ : Q ∈ productLeaves I N)
    (hR : R ∈ productLeaves I N) {x : ProductPoint d}
    (hxQ : x ∈ productBox Q) (hxR : x ∈ productBox R) : Q = R := by
  funext i
  exact (level (I i) (N i)).eq_of_mem_of_mem
    (Fintype.mem_piFinset.mp hQ i) (Fintype.mem_piFinset.mp hR i)
    ((mem_productBox Q x).mp hxQ i) ((mem_productBox R x).mp hxR i)

/-- The paper's pointwise constancy hypothesis on smallest product cubes. -/
def ProductLeafConstant (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) : Prop :=
  ∀ Q ∈ productLeaves I N, ∀ x ∈ productBox Q, ∀ y ∈ productBox Q, f x = f y

/-- The finite-indicator representation is an equality of functions. -/
theorem product_step_representation (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f) :
    (productBox I).indicator f =
      ∑ Q ∈ productLeaves I N,
        (productBox Q).indicator (fun _ => f (fun i => (Q i).upper)) := by
  funext x
  simp only [Finset.sum_apply]
  by_cases hx : x ∈ productBox I
  · obtain ⟨Q, hQ, hxQ⟩ := productLeaves_cover I N x hx
    rw [Finset.sum_eq_single Q]
    · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hxQ]
      exact hf Q hQ x hxQ _ ((mem_productBox Q _).mpr (fun i => (Q i).upper_mem))
    · intro R hR hRQ
      have hxR : x ∉ productBox R := fun h => hRQ (productLeaves_unique hR hQ h hxQ)
      exact Set.indicator_of_notMem hxR _
    · simp [hQ]
  · rw [Set.indicator_of_notMem hx]
    symm
    exact Finset.sum_eq_zero (fun Q hQ =>
      Set.indicator_of_notMem (fun hxQ => hx (productLeaves_subset hQ hxQ)) _)

theorem measurable_product_localization (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f) :
    Measurable ((productBox I).indicator f) := by
  rw [product_step_representation I N f hf]
  have hm : Measurable (fun x => ∑ Q ∈ productLeaves I N,
      (productBox Q).indicator (fun _ => f (fun i => (Q i).upper)) x) :=
    Finset.measurable_sum _ (fun Q _ =>
      measurable_const.indicator (measurableSet_productBox Q))
  convert hm using 1
  ext x
  simp only [Finset.sum_apply]

theorem bounded_product_localization (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |(productBox I).indicator f x| ≤ C := by
  refine ⟨∑ Q ∈ productLeaves I N, |f (fun i => (Q i).upper)|,
    Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro x
  rw [product_step_representation I N f hf]
  simp only [Finset.sum_apply]
  calc
    _ ≤ ∑ Q ∈ productLeaves I N,
        |(productBox Q).indicator (fun _ => f (fun i => (Q i).upper)) x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro Q _
      by_cases hx : x ∈ productBox Q
      · simp [hx]
      · simp [hx, abs_nonneg]

/-- Bounded measurable inputs have integrable coordinate slices on boxes. -/
theorem integrable_coordinateSlice (f : ProductPoint d → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ x, |f x| ≤ C) (i : Fin m) (Q : Box (Fin (d i)))
    (x : ProductPoint d) :
    IntegrableOn (fun y => f (Function.update x i y)) (Q : Set (Fin (d i) → ℝ))
      volume := by
  let : IsFiniteMeasure (volume.restrict (Q : Set (Fin (d i) → ℝ))) :=
    isFiniteMeasure_restrict.mpr (Q.measure_coe_lt_top volume).ne
  exact (integrable_const C).mono' (hf.comp (measurable_update x)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => by simpa [Real.norm_eq_abs] using hC _))

/-- The two-coordinate Fubini hypothesis is derived from measurability and boundedness. -/
theorem integrable_twoCoordinateSlice (f : ProductPoint d → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ x, |f x| ≤ C) (i j : Fin m)
    (Q : Box (Fin (d i))) (R : Box (Fin (d j))) (x : ProductPoint d) :
    Integrable (fun yz : (Fin (d i) → ℝ) × (Fin (d j) → ℝ) =>
      f (Function.update (Function.update x i yz.1) j yz.2))
      ((volume.restrict (Q : Set (Fin (d i) → ℝ))).prod
        (volume.restrict (R : Set (Fin (d j) → ℝ)))) := by
  let : IsFiniteMeasure (volume.restrict (Q : Set (Fin (d i) → ℝ))) :=
    isFiniteMeasure_restrict.mpr (Q.measure_coe_lt_top volume).ne
  let : IsFiniteMeasure (volume.restrict (R : Set (Fin (d j) → ℝ))) :=
    isFiniteMeasure_restrict.mpr (R.measure_coe_lt_top volume).ne
  have hu : Measurable (fun yz : (Fin (d i) → ℝ) × (Fin (d j) → ℝ) =>
      Function.update (Function.update x i yz.1) j yz.2) :=
    measurable_update'.comp (((measurable_update x).comp measurable_fst).prodMk measurable_snd)
  exact (integrable_const C).mono' (hf.comp hu).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun yz => by simpa [Real.norm_eq_abs] using hC _))

/-- Coordinate averages commute for the zero-extended finite input.
There is no separate integrability assumption in this finite realization. -/
theorem coordinateAverage_commute_productStep
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (i j : Fin m) (hij : i ≠ j) (Q : Box (Fin (d i))) (R : Box (Fin (d j))) :
    coordinateAverage i Q (coordinateAverage j R ((productBox I).indicator f)) =
      coordinateAverage j R (coordinateAverage i Q ((productBox I).indicator f)) := by
  obtain ⟨C, _, hC⟩ := bounded_product_localization I N f hf
  apply coordinateAverage_commute i j hij Q R
  intro x
  exact integrable_twoCoordinateSlice _ (measurable_product_localization I N f hf)
    C hC i j Q R x

end ReyZygmund.Geometry
