import ReyZygmund.Geometry.ProductOperators
import Mathlib.Data.Fintype.Pi

/-!
# Finite product step functions

After restriction to the top rectangle and zero extension, a function constant on
the smallest product cubes has a finite-indicator representation. This gives
measurability, boundedness and slice integrability. Coordinate cutoffs may differ.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

@[simp] theorem mem_productRectangle (Q : ∀ i, Box (Fin (d i))) (x : ProductPoint d) :
    x ∈ productRectangle Q ↔ ∀ i, x i ∈ Q i := Iff.rfl

/-- The coordinate-membership description is the Cartesian product of the boxes. -/
theorem productRectangle_eq_pi (Q : ∀ i, Box (Fin (d i))) :
    productRectangle Q = Set.pi Set.univ (fun i => (Q i : Set (Fin (d i) → ℝ))) := by
  ext x
  simp [productRectangle, Set.pi]

theorem measurableSet_productRectangle (Q : ∀ i, Box (Fin (d i))) :
    MeasurableSet (productRectangle Q) := by
  rw [productRectangle_eq_pi]
  exact MeasurableSet.univ_pi (fun i => (Q i).measurableSet_coe)

/-- Restricting Lebesgue measure to a rectangle restricts each coordinate factor. -/
theorem restrict_volume_productRectangle (Q : ∀ i, Box (Fin (d i))) :
    volume.restrict (productRectangle Q) =
      Measure.pi (fun i => volume.restrict (Q i : Set (Fin (d i) → ℝ))) := by
  rw [productRectangle_eq_pi]
  exact Measure.restrict_pi_pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
    (fun i => (Q i : Set (Fin (d i) → ℝ)))

/-- The volume of a rectangle is the product of its factor volumes. -/
theorem productRectangle_volume (Q : ∀ i, Box (Fin (d i))) :
    volume (productRectangle Q) = ∏ i, volume (Q i : Set (Fin (d i) → ℝ)) := by
  rw [productRectangle_eq_pi]
  exact Measure.pi_pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
    (fun i => (Q i : Set (Fin (d i) → ℝ)))

theorem productRectangle_volume_real (Q : ∀ i, Box (Fin (d i))) :
    volume.real (productRectangle Q) =
      ∏ i, volume.real (Q i : Set (Fin (d i) → ℝ)) := by
  simp only [measureReal_def, productRectangle_volume, ENNReal.toReal_prod]

/-- Rectangle volume is positive. -/
theorem productRectangle_volume_pos (Q : ∀ i, Box (Fin (d i))) :
    0 < volume.real (productRectangle Q) := by
  rw [productRectangle_volume_real]
  exact Finset.prod_pos (fun i _ => box_volume_pos (Q i))

/-- The Lebesgue volume of a rectangle is finite. -/
theorem productRectangle_volume_lt_top (Q : ∀ i, Box (Fin (d i))) :
    volume (productRectangle Q) < ∞ := by
  rw [productRectangle_volume]
  exact ENNReal.prod_lt_top (fun i _ => (Q i).measure_coe_lt_top volume)

/-- Independent finite cutoffs in the coordinate trees. -/
noncomputable def productLeaves (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) :
    Finset (∀ i, Box (Fin (d i))) :=
  Fintype.piFinset (fun i => leaves (I i) (N i))

theorem productLeaves_cover (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (x : ProductPoint d) (hx : x ∈ productRectangle I) :
    ∃ Q ∈ productLeaves I N, x ∈ productRectangle Q := by
  have hi (i : Fin m) := level_isPartition (I i) (N i) (x i) ((mem_productRectangle I x).mp hx i)
  choose Q hQ hxQ using hi
  exact ⟨Q, Fintype.mem_piFinset.mpr hQ, (mem_productRectangle Q x).mpr hxQ⟩

theorem productLeaves_subset {I : ∀ i, Box (Fin (d i))} {N : Fin m → ℕ}
    {Q : ∀ i, Box (Fin (d i))} (hQ : Q ∈ productLeaves I N) :
    productRectangle Q ⊆ productRectangle I := by
  intro x hx
  apply (mem_productRectangle I x).mpr
  intro i
  exact (level (I i) (N i)).le_of_mem (Fintype.mem_piFinset.mp hQ i)
    ((mem_productRectangle Q x).mp hx i)

theorem productLeaves_unique {I : ∀ i, Box (Fin (d i))} {N : Fin m → ℕ}
    {Q R : ∀ i, Box (Fin (d i))} (hQ : Q ∈ productLeaves I N)
    (hR : R ∈ productLeaves I N) {x : ProductPoint d}
    (hxQ : x ∈ productRectangle Q) (hxR : x ∈ productRectangle R) : Q = R := by
  funext i
  exact (level (I i) (N i)).eq_of_mem_of_mem
    (Fintype.mem_piFinset.mp hQ i) (Fintype.mem_piFinset.mp hR i)
    ((mem_productRectangle Q x).mp hxQ i) ((mem_productRectangle R x).mp hxR i)

/-- The paper's pointwise constancy hypothesis on smallest product cubes. -/
def ProductLeafConstant (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) : Prop :=
  ∀ Q ∈ productLeaves I N, ∀ x ∈ productRectangle Q, ∀ y ∈ productRectangle Q, f x = f y

/-- The finite-indicator representation is an equality of functions. -/
theorem product_step_representation (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f) :
    (productRectangle I).indicator f =
      ∑ Q ∈ productLeaves I N,
        (productRectangle Q).indicator (fun _ => f (fun i => (Q i).upper)) := by
  funext x
  simp only [Finset.sum_apply]
  by_cases hx : x ∈ productRectangle I
  · obtain ⟨Q, hQ, hxQ⟩ := productLeaves_cover I N x hx
    rw [Finset.sum_eq_single Q]
    · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hxQ]
      exact hf Q hQ x hxQ _ ((mem_productRectangle Q _).mpr (fun i => (Q i).upper_mem))
    · intro R hR hRQ
      have hxR : x ∉ productRectangle R := fun h => hRQ (productLeaves_unique hR hQ h hxQ)
      exact Set.indicator_of_notMem hxR _
    · simp [hQ]
  · rw [Set.indicator_of_notMem hx]
    symm
    exact Finset.sum_eq_zero (fun Q hQ =>
      Set.indicator_of_notMem (fun hxQ => hx (productLeaves_subset hQ hxQ)) _)

theorem measurable_product_localization (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f) :
    Measurable ((productRectangle I).indicator f) := by
  rw [product_step_representation I N f hf]
  have hm : Measurable (fun x => ∑ Q ∈ productLeaves I N,
      (productRectangle Q).indicator (fun _ => f (fun i => (Q i).upper)) x) :=
    Finset.measurable_sum _ (fun Q _ =>
      measurable_const.indicator (measurableSet_productRectangle Q))
  convert hm using 1
  ext x
  simp only [Finset.sum_apply]

theorem bounded_product_localization (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |(productRectangle I).indicator f x| ≤ C := by
  refine ⟨∑ Q ∈ productLeaves I N, |f (fun i => (Q i).upper)|,
    Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro x
  rw [product_step_representation I N f hf]
  simp only [Finset.sum_apply]
  calc
    _ ≤ ∑ Q ∈ productLeaves I N,
        |(productRectangle Q).indicator (fun _ => f (fun i => (Q i).upper)) x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro Q _
      by_cases hx : x ∈ productRectangle Q
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

/-- Coordinate averages commute for the zero-extended finite input. -/
theorem coordinateAverage_commute_productStep
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (i j : Fin m) (hij : i ≠ j) (Q : Box (Fin (d i))) (R : Box (Fin (d j))) :
    coordinateAverage i Q (coordinateAverage j R ((productRectangle I).indicator f)) =
      coordinateAverage j R (coordinateAverage i Q ((productRectangle I).indicator f)) := by
  obtain ⟨C, _, hC⟩ := bounded_product_localization I N f hf
  apply coordinateAverage_commute i j hij Q R
  intro x
  exact integrable_twoCoordinateSlice _ (measurable_product_localization I N f hf)
    C hC i j Q R x

end ReyZygmund.Geometry
