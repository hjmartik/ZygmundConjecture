import ReyZygmund.Geometry.ProductPartitions
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Algebra.Module.Submodule.Basic

/-! # Linear coordinate operators

Bounded measurable functions are closed under finite sums and compositions of the
coordinate operators, with the integrability required for their identities. Finite
step functions enter this space by zero extension. The empty product of operators
is the identity, and operators in distinct coordinates commute.


-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} (d : Fin m → ℕ)

/-- A concrete submodule of real-valued functions, used only to package closure. -/
def boundedMeasurableFunctions : Submodule ℝ (ProductPoint d → ℝ) where
  carrier := {f | Measurable f ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C}
  zero_mem' := ⟨measurable_const, 0, le_rfl, by simp⟩
  add_mem' := by
    rintro f g ⟨hf, C, hC, hfb⟩ ⟨hg, D, hD, hgb⟩
    refine ⟨hf.add hg, C + D, add_nonneg hC hD, ?_⟩
    intro x
    exact (abs_add_le (f x) (g x)).trans (add_le_add (hfb x) (hgb x))
  smul_mem' := by
    rintro c f ⟨hf, C, hC, hfb⟩
    refine ⟨measurable_const.mul hf, |c| * C, mul_nonneg (abs_nonneg c) hC, ?_⟩
    intro x
    simpa only [Pi.smul_apply, smul_eq_mul, abs_mul] using
      mul_le_mul_of_nonneg_left (hfb x) (abs_nonneg c)

variable {d}

/-- A finite input, localized to the top rectangle. -/
noncomputable def finiteInput (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f) :
    boundedMeasurableFunctions d :=
  ⟨(productBox I).indicator f, measurable_product_localization I N f hf,
    bounded_product_localization I N f hf⟩

/-- The coordinate average as a linear map on its proved closed function class. -/
noncomputable def averageMap (i : Fin m) (Q : Box (Fin (d i))) :
    Module.End ℝ (boundedMeasurableFunctions d) where
  toFun f := ⟨coordinateAverage i Q f.1, coordinateAverage_measurable i Q f.1 f.2.1, by
    obtain ⟨C, hC, hb⟩ := f.2.2
    exact ⟨C, hC, coordinateAverage_abs_le i Q f.1 C hC hb⟩⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    obtain ⟨C, _, hC⟩ := f.2.2
    obtain ⟨D, _, hD⟩ := g.2.2
    have hfi := integrable_coordinateSlice f.1 f.2.1 C hC i Q x
    have hgi := integrable_coordinateSlice g.1 g.2.1 D hD i Q x
    by_cases hx : x i ∈ Q
    · change coordinateAverage i Q (f.1 + g.1) x =
        coordinateAverage i Q f.1 x + coordinateAverage i Q g.1 x
      simp only [coordinateAverage_of_mem i Q _ x hx, Pi.add_apply]
      rw [integral_add hfi hgi, add_div]
    · simp [coordinateAverage, boxAverage, hx]
  map_smul' c f := by
    apply Subtype.ext
    funext x
    by_cases hx : x i ∈ Q
    · simp [coordinateAverage, boxAverage, hx, integral_const_mul, mul_div_assoc]
    · simp [coordinateAverage, boxAverage, hx]

@[simp] theorem averageMap_apply (i : Fin m) (Q : Box (Fin (d i)))
    (f : boundedMeasurableFunctions d) :
    (averageMap i Q f).1 = coordinateAverage i Q f.1 := rfl

/-- The difference map uses exactly the same child-minus-parent formula. -/
noncomputable def differenceMap (i : Fin m) (Q : Box (Fin (d i))) :
    Module.End ℝ (boundedMeasurableFunctions d) :=
  (∑ R ∈ (Prepartition.splitCenter Q).boxes, averageMap i R) - averageMap i Q

@[simp] theorem differenceMap_apply (i : Fin m) (Q : Box (Fin (d i)))
    (f : boundedMeasurableFunctions d) :
    (differenceMap i Q f).1 = coordinateDifference i Q f.1 := by
  funext x
  simp [differenceMap, coordinateDifference, Finset.sum_apply]

theorem averageMap_commute (i j : Fin m) (hij : i ≠ j)
    (Q : Box (Fin (d i))) (R : Box (Fin (d j))) :
    Commute (averageMap i Q) (averageMap j R) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  obtain ⟨C, _, hb⟩ := f.2.2
  exact coordinateAverage_commute i j hij Q R f.1
    (fun x => integrable_twoCoordinateSlice f.1 f.2.1 C hb i j Q R x)

theorem differenceMap_commute (i j : Fin m) (hij : i ≠ j)
    (Q : Box (Fin (d i))) (R : Box (Fin (d j))) :
    Commute (differenceMap i Q) (differenceMap j R) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  obtain ⟨C, hC, hb⟩ := f.2.2
  simpa only [Module.End.mul_apply, differenceMap_apply] using
    coordinateDifference_commute i j hij Q R f.1 f.2.1 C hC hb

theorem averageMap_differenceMap_commute (i j : Fin m) (hij : i ≠ j)
    (Q : Box (Fin (d i))) (R : Box (Fin (d j))) :
    Commute (averageMap i Q) (differenceMap j R) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  obtain ⟨C, hC, hb⟩ := f.2.2
  simpa only [Module.End.mul_apply, averageMap_apply, differenceMap_apply] using
    coordinateAverage_difference_commute i j hij Q R f.1 f.2.1 C hC hb

/-- A product of differences, indexed by a finite set of distinct coordinates. -/
noncomputable def productDifferenceMap (A : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) : Module.End ℝ (boundedMeasurableFunctions d) :=
  A.noncommProd (fun i => differenceMap i (Q i))
    (fun i _ j _ hij => differenceMap_commute i j hij (Q i) (Q j))

/-- The corresponding product of coordinate averages. -/
noncomputable def productAverageMap (A : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) : Module.End ℝ (boundedMeasurableFunctions d) :=
  A.noncommProd (fun i => averageMap i (Q i))
    (fun i _ j _ hij => averageMap_commute i j hij (Q i) (Q j))

@[simp] theorem productDifferenceMap_empty (Q : ∀ i, Box (Fin (d i))) :
    productDifferenceMap ∅ Q = 1 := rfl

@[simp] theorem productAverageMap_empty (Q : ∀ i, Box (Fin (d i))) :
    productAverageMap ∅ Q = 1 := rfl

theorem productDifferenceMap_insert (A : Finset (Fin m)) (i : Fin m) (hi : i ∉ A)
    (Q : ∀ i, Box (Fin (d i))) :
    productDifferenceMap (insert i A) Q = differenceMap i (Q i) * productDifferenceMap A Q := by
  exact Finset.noncommProd_insert_of_notMem A i _ _ hi

theorem productAverageMap_insert (A : Finset (Fin m)) (i : Fin m) (hi : i ∉ A)
    (Q : ∀ i, Box (Fin (d i))) :
    productAverageMap (insert i A) Q = averageMap i (Q i) * productAverageMap A Q := by
  exact Finset.noncommProd_insert_of_notMem A i _ _ hi

end ReyZygmund.Geometry
