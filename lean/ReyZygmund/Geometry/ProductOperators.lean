import ReyZygmund.Geometry.FiniteAverages
import Mathlib.MeasureTheory.Integral.Prod

/-! # Coordinate averages and differences

Each coordinate is a Euclidean space of the specified dimension. A coordinate
average integrates in that variable while fixing the others. The identities state
their integrability hypotheses explicitly; finite step functions satisfy these
hypotheses in the paper's finite argument.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

/-- The product of the paper's Euclidean coordinate factors. -/
abbrev ProductPoint {m : ℕ} (d : Fin m → ℕ) := ∀ i, Fin (d i) → ℝ

variable {m : ℕ} {d : Fin m → ℕ}

/-- The supported average in one coordinate, using Lebesgue integration. -/
noncomputable def coordinateAverage (i : Fin m) (Q : Box (Fin (d i)))
    (f : ProductPoint d → ℝ) (x : ProductPoint d) : ℝ :=
  boxAverage Q (fun y => f (Function.update x i y)) (x i)

/-- Child averages minus the parent average in one coordinate. -/
noncomputable def coordinateDifference (i : Fin m) (Q : Box (Fin (d i)))
    (f : ProductPoint d → ℝ) : ProductPoint d → ℝ :=
  (∑ R ∈ (Prepartition.splitCenter Q).boxes, coordinateAverage i R f) -
    coordinateAverage i Q f

theorem coordinateAverage_of_mem (i : Fin m) (Q : Box (Fin (d i)))
    (f : ProductPoint d → ℝ) (x : ProductPoint d) (hx : x i ∈ Q) :
    coordinateAverage i Q f x =
      (∫ y in (Q : Set (Fin (d i) → ℝ)), f (Function.update x i y)) /
        volume.real (Q : Set (Fin (d i) → ℝ)) := by
  simp [coordinateAverage, boxAverage, hx]

theorem coordinateAverage_of_notMem (i : Fin m) (Q : Box (Fin (d i)))
    (f : ProductPoint d → ℝ) (x : ProductPoint d) (hx : x i ∉ Q) :
    coordinateAverage i Q f x = 0 := by
  simp [coordinateAverage, boxAverage, hx]

theorem coordinateDifference_slice (i : Fin m) (Q : Box (Fin (d i)))
    (f : ProductPoint d → ℝ) (x : ProductPoint d) :
    coordinateDifference i Q f x =
      boxDifference Q (fun y => f (Function.update x i y)) (x i) := by
  simp [coordinateDifference, boxDifference, coordinateAverage]

theorem coordinateAverage_idempotent (i : Fin m) (Q : Box (Fin (d i)))
    (f : ProductPoint d → ℝ) :
    coordinateAverage i Q (coordinateAverage i Q f) = coordinateAverage i Q f := by
  funext x
  by_cases hx : x i ∈ Q
  · rw [coordinateAverage_of_mem i Q _ x hx]
    have hc : ∀ y ∈ Q, coordinateAverage i Q f (Function.update x i y) =
        coordinateAverage i Q f x := by
      intro y hy
      simp [coordinateAverage, boxAverage, hy, hx]
    rw [setIntegral_congr_fun Q.measurableSet_coe hc, setIntegral_const, smul_eq_mul]
    exact mul_div_cancel_left₀ _ (ne_of_gt (box_volume_pos Q))
  · simp [coordinateAverage, boxAverage, hx]

/-- Joint measurability comes from parameterized integration, not a choice of slices. -/
theorem coordinateAverage_measurable (i : Fin m) (Q : Box (Fin (d i)))
    (f : ProductPoint d → ℝ) (hf : Measurable f) :
    Measurable (coordinateAverage i Q f) := by
  have hm : Measurable (fun xy : ProductPoint d × (Fin (d i) → ℝ) =>
      f (Function.update xy.1 i xy.2)) := hf.comp measurable_update'
  have hi : Measurable (fun x : ProductPoint d =>
      (∫ y in (Q : Set (Fin (d i) → ℝ)), f (Function.update x i y)) /
        volume.real (Q : Set (Fin (d i) → ℝ))) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable.div_const _
  convert hi.indicator (Q.measurableSet_coe.preimage (measurable_pi_apply i)) using 1
  funext x
  by_cases hx : x i ∈ Q <;> simp [coordinateAverage, boxAverage, hx]

theorem coordinateAverage_sub (i : Fin m) (Q : Box (Fin (d i)))
    (f g : ProductPoint d → ℝ)
    (hf : ∀ x, IntegrableOn (fun y => f (Function.update x i y))
      (Q : Set (Fin (d i) → ℝ)) volume)
    (hg : ∀ x, IntegrableOn (fun y => g (Function.update x i y))
      (Q : Set (Fin (d i) → ℝ)) volume) :
    coordinateAverage i Q (f - g) = coordinateAverage i Q f - coordinateAverage i Q g := by
  funext x
  by_cases hx : x i ∈ Q
  · simp only [Pi.sub_apply, coordinateAverage_of_mem i Q _ x hx]
    rw [integral_sub (hf x) (hg x), sub_div]
  · simp [coordinateAverage, boxAverage, hx]

theorem coordinateAverage_finsetSum {κ : Type*} (s : Finset κ)
    (i : Fin m) (Q : Box (Fin (d i))) (f : κ → ProductPoint d → ℝ)
    (hf : ∀ k ∈ s, ∀ x, IntegrableOn (fun y => f k (Function.update x i y))
      (Q : Set (Fin (d i) → ℝ)) volume) :
    coordinateAverage i Q (∑ k ∈ s, f k) = ∑ k ∈ s, coordinateAverage i Q (f k) := by
  funext x
  by_cases hx : x i ∈ Q
  · simp only [coordinateAverage_of_mem i Q _ x hx, Finset.sum_apply]
    rw [integral_finsetSum s (fun k hk => hf k hk x), Finset.sum_div]
  · simp [coordinateAverage, boxAverage, hx]

/-- Fubini in two different coordinates. The hypothesis is a local
integrability condition, later supplied by the finite step-function realization. -/
theorem coordinateAverage_commute (i j : Fin m) (hij : i ≠ j)
    (Q : Box (Fin (d i))) (R : Box (Fin (d j))) (f : ProductPoint d → ℝ)
    (hf : ∀ x : ProductPoint d, Integrable
      (fun yz : (Fin (d i) → ℝ) × (Fin (d j) → ℝ) =>
        f (Function.update (Function.update x i yz.1) j yz.2))
      ((volume.restrict (Q : Set (Fin (d i) → ℝ))).prod
        (volume.restrict (R : Set (Fin (d j) → ℝ))))) :
    coordinateAverage i Q (coordinateAverage j R f) =
      coordinateAverage j R (coordinateAverage i Q f) := by
  funext x
  by_cases hxQ : x i ∈ Q
  · by_cases hxR : x j ∈ R
    · have hs := integral_integral_swap
        (f := fun y z => f (Function.update (Function.update x i y) j z)) (hf x)
      simp_rw [Function.update_comm hij] at hs
      simpa [coordinateAverage, boxAverage, hxQ, hxR, hij, hij.symm,
        integral_div, div_div, mul_comm, Function.update_comm hij] using
        congrArg (fun z : ℝ => z /
          (volume.real (Q : Set (Fin (d i) → ℝ)) *
            volume.real (R : Set (Fin (d j) → ℝ)))) hs
    · simp [coordinateAverage, boxAverage, hxQ, hxR, hij, hij.symm]
  · simp [coordinateAverage, boxAverage, hxQ, hij, hij.symm]

end ReyZygmund.Geometry
