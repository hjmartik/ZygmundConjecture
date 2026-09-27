/-
The private partial-integral helpers adapt the finite-product decomposition in
Mathlib/MeasureTheory/Integral/Marginal.lean, at Mathlib revision
5ed2965256430c3649e86755f9576b54eca72435.

Original notice for those adapted portions:
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in Mathlib's LICENSE.
Authors: Floris van Doorn, Heather Macbeth

Modifications: specialize to restricted Lebesgue measures on boxes and
replace the nonnegative integral by the signed Bochner integral, deriving its
integrability from a bound. The selected-coordinate averaging induction
and normalization below connect this decomposition to the project operators.
-/

import ReyZygmund.Geometry.ProductMaps
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The integral represented by all coordinate averages

The coordinate maps act on bounded measurable functions. The proof uses
finite-product Fubini for the Lebesgue measures restricted to the coordinate
boxes. Empty products and zero-dimensional coordinate boxes are included.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private noncomputable def partialIntegral (R : ∀ i, Box (Fin (d i)))
    (A : Finset (Fin m)) (f : ProductPoint d → ℝ) (x : ProductPoint d) : ℝ :=
  ∫ y : ∀ i : A, Fin (d i) → ℝ, f (Function.updateFinset x A y)
    ∂Measure.pi (fun i : A => volume.restrict (R i : Set (Fin (d i) → ℝ)))

private theorem integrable_bounded_comp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (F : boundedMeasurableFunctions d)
    (u : α → ProductPoint d) (hu : Measurable u) :
    Integrable (fun a => F.1 (u a)) μ := by
  obtain ⟨C, _, hC⟩ := F.2.2
  exact (integrable_const C).mono' (F.2.1.comp hu).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun a => by
      simpa only [Real.norm_eq_abs] using hC (u a)))

private theorem partialIntegral_empty (R : ∀ i, Box (Fin (d i)))
    (f : ProductPoint d → ℝ) (x : ProductPoint d) :
    partialIntegral R ∅ f x = f x := by
  simp only [partialIntegral, Function.updateFinset_empty, integral_const, smul_eq_mul]
  rw [measureReal_def, Measure.pi_univ]
  simp

private theorem partialIntegral_singleton (R : ∀ i, Box (Fin (d i)))
    (i : Fin m) (f : ProductPoint d → ℝ) (x : ProductPoint d) :
    partialIntegral R {i} f x =
      ∫ y in (R i : Set (Fin (d i) → ℝ)), f (Function.update x i y) := by
  let α : Type := ({i} : Finset (Fin m))
  let μ : ∀ j : Fin m, Measure (Fin (d j) → ℝ) :=
    fun j => volume.restrict (R j : Set (Fin (d j) → ℝ))
  let e := (MeasurableEquiv.piUnique (fun j : α => Fin (d j) → ℝ)).symm
  calc
    partialIntegral R {i} f x =
        ∫ y : Fin (d (default : α)) → ℝ,
          f (Function.updateFinset x {i} (e y)) ∂μ (default : α) := by
      exact ((measurePreserving_piUnique (fun j : α => μ j)).symm _
        |>.integral_comp' (fun y => f (Function.updateFinset x {i} y))).symm
    _ = ∫ y in (R i : Set (Fin (d i) → ℝ)), f (Function.update x i y) := by
      simp [Function.update_eq_updateFinset]
      rfl

private theorem partialIntegral_union (R : ∀ i, Box (Fin (d i)))
    (F : boundedMeasurableFunctions d) (s t : Finset (Fin m))
    (hst : Disjoint s t) (x : ProductPoint d) :
    partialIntegral R (s ∪ t) F.1 x =
      partialIntegral R s (partialIntegral R t F.1) x := by
  let μ : ∀ i : Fin m, Measure (Fin (d i) → ℝ) :=
    fun i => volume.restrict (R i : Set (Fin (d i) → ℝ))
  let : ∀ i, IsFiniteMeasure (μ i) := fun i =>
    isFiniteMeasure_restrict.mpr ((R i).measure_coe_lt_top volume).ne
  let e := MeasurableEquiv.piFinsetUnion (fun i : Fin m => Fin (d i) → ℝ) hst
  have he := measurePreserving_piFinsetUnion hst μ
  have hf : Integrable
      (fun y : ((i : s) → Fin (d i) → ℝ) × ((j : t) → Fin (d j) → ℝ) =>
        F.1 (Function.updateFinset x (s ∪ t) (e y)))
      ((Measure.pi (fun i : s => μ i)).prod (Measure.pi (fun j : t => μ j))) :=
    integrable_bounded_comp _ F _ (measurable_updateFinset.comp e.measurable)
  calc
    partialIntegral R (s ∪ t) F.1 x =
        ∫ y : ((i : s) → Fin (d i) → ℝ) × ((j : t) → Fin (d j) → ℝ),
          F.1 (Function.updateFinset x (s ∪ t) (e y))
          ∂(Measure.pi (fun i : s => μ i)).prod (Measure.pi (fun j : t => μ j)) := by
      exact (he.integral_comp' (fun y => F.1 (Function.updateFinset x (s ∪ t) y))).symm
    _ = ∫ y : (i : s) → Fin (d i) → ℝ,
        ∫ z : (j : t) → Fin (d j) → ℝ,
          F.1 (Function.updateFinset x (s ∪ t) (e (y, z)))
          ∂Measure.pi (fun j : t => μ j) ∂Measure.pi (fun i : s => μ i) :=
      integral_prod _ hf
    _ = partialIntegral R s (partialIntegral R t F.1) x := by
      simp_rw [partialIntegral, Function.updateFinset_updateFinset hst]
      rfl

private theorem partialIntegral_insert (R : ∀ i, Box (Fin (d i)))
    (F : boundedMeasurableFunctions d) (A : Finset (Fin m))
    (i : Fin m) (hi : i ∉ A) (x : ProductPoint d) :
    partialIntegral R (insert i A) F.1 x =
      ∫ y in (R i : Set (Fin (d i) → ℝ)),
        partialIntegral R A F.1 (Function.update x i y) := by
  rw [Finset.insert_eq,
    partialIntegral_union R F {i} A (Finset.disjoint_singleton_left.mpr hi),
    partialIntegral_singleton]

private theorem partialIntegral_univ (R : ∀ i, Box (Fin (d i)))
    (f : ProductPoint d → ℝ) (x : ProductPoint d) :
    partialIntegral R Finset.univ f x = ∫ y in productBox R, f y := by
  let μ : ∀ i : Fin m, Measure (Fin (d i) → ℝ) :=
    fun i => volume.restrict (R i : Set (Fin (d i) → ℝ))
  let : ∀ i, IsFiniteMeasure (μ i) := fun i =>
    isFiniteMeasure_restrict.mpr ((R i).measure_coe_lt_top volume).ne
  let e : (Finset.univ : Finset (Fin m)) ≃ Fin m :=
    Equiv.subtypeUnivEquiv Finset.mem_univ
  have hupdate (y : ∀ i : (Finset.univ : Finset (Fin m)), Fin (d i) → ℝ) :
      Function.updateFinset x Finset.univ y =
        MeasurableEquiv.piCongrLeft (fun i : Fin m => Fin (d i) → ℝ) e y := by
    funext i
    rw [Function.updateFinset_univ_apply]
    exact (MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun i : Fin m => Fin (d i) → ℝ) e y
      ⟨i, Finset.mem_univ i⟩).symm
  have hrestrict : volume.restrict (productBox R) = Measure.pi μ :=
    Measure.restrict_pi_pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
      (fun i => (R i : Set (Fin (d i) → ℝ)))
  calc
    partialIntegral R Finset.univ f x =
        ∫ y : ∀ i : (Finset.univ : Finset (Fin m)), Fin (d i) → ℝ,
          f (MeasurableEquiv.piCongrLeft (fun i : Fin m => Fin (d i) → ℝ) e y)
          ∂Measure.pi (fun i : (Finset.univ : Finset (Fin m)) => μ i) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => congrArg f (hupdate y))
    _ = ∫ y, f y ∂Measure.pi μ :=
      (measurePreserving_piCongrLeft μ e).integral_comp' f
    _ = ∫ y in productBox R, f y := by rw [hrestrict]

private theorem productBox_volume_real (R : ∀ i, Box (Fin (d i))) :
    volume.real (productBox R) =
      ∏ i, volume.real (R i : Set (Fin (d i) → ℝ)) := by
  change (Measure.pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
    (Set.pi Set.univ (fun i => (R i : Set (Fin (d i) → ℝ))))).toReal =
      ∏ i, (volume (R i : Set (Fin (d i) → ℝ))).toReal
  rw [Measure.pi_pi, ENNReal.toReal_prod]

private theorem productAverageMap_eq_partialIntegral
    (R : ∀ i, Box (Fin (d i))) (F : boundedMeasurableFunctions d)
    (A : Finset (Fin m)) (x : ProductPoint d) :
    (productAverageMap A R F).1 x =
      if ∀ i ∈ A, x i ∈ R i then
        partialIntegral R A F.1 x /
          ∏ i ∈ A, volume.real (R i : Set (Fin (d i) → ℝ))
      else 0 := by
  induction A using Finset.induction generalizing x with
  | empty => simp [partialIntegral_empty]
  | @insert i A hi ih =>
    rw [productAverageMap_insert A i hi R, Module.End.mul_apply, averageMap_apply]
    by_cases hx : x i ∈ R i
    · rw [coordinateAverage_of_mem i (R i) _ x hx]
      have htail (y : Fin (d i) → ℝ) :
          (∀ j ∈ A, Function.update x i y j ∈ R j) ↔ ∀ j ∈ A, x j ∈ R j := by
        refine forall_congr' (fun j => forall_congr' fun hj => ?_)
        have hji : j ≠ i := by
          intro h
          subst j
          exact hi hj
        simp [hji]
      by_cases hA : ∀ j ∈ A, x j ∈ R j
      · have hfull : ∀ j ∈ insert i A, x j ∈ R j := by
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact hx
          · exact hA j hj
        have hfun :
            (fun y => (productAverageMap A R F).1 (Function.update x i y)) =
              fun y => partialIntegral R A F.1 (Function.update x i y) /
                ∏ j ∈ A, volume.real (R j : Set (Fin (d j) → ℝ)) := by
          funext y
          rw [ih, ite_eq_left ((htail y).mpr hA)]
        rw [hfun, integral_div, ← partialIntegral_insert R F A i hi x,
          ite_eq_left hfull, Finset.prod_insert hi, div_div, mul_comm]
      · have hfull : ¬∀ j ∈ insert i A, x j ∈ R j := by
          intro h
          exact hA (fun j hj => h j (Finset.mem_insert_of_mem hj))
        have hfun :
            (fun y => (productAverageMap A R F).1 (Function.update x i y)) =
              fun _ : Fin (d i) → ℝ => (0 : ℝ) := by
          funext y
          rw [ih, ite_eq_right (fun h => hA ((htail y).mp h))]
        rw [hfun, integral_zero, zero_div, ite_eq_right hfull]
    · rw [coordinateAverage_of_notMem i (R i) _ x hx]
      have hfull : ¬∀ j ∈ insert i A, x j ∈ R j := by
        intro h
        exact hx (h i (Finset.mem_insert_self i A))
      rw [ite_eq_right hfull]

/-- Averaging in every coordinate is exactly the supported normalized Lebesgue
integral over the product rectangle, for arbitrary signed bounded measurable inputs. -/
theorem productAverageMap_univ_eq_integral (R : ∀ i, Box (Fin (d i)))
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) :
    (productAverageMap Finset.univ R F).1 x =
      (productBox R).indicator
        (fun _ => (∫ y in productBox R, F.1 y) / volume.real (productBox R)) x := by
  rw [productAverageMap_eq_partialIntegral, partialIntegral_univ,
    ← productBox_volume_real]
  by_cases hx : x ∈ productBox R
  · have hfull : ∀ i ∈ (Finset.univ : Finset (Fin m)), x i ∈ R i :=
      fun i _ => (mem_productBox R x).mp hx i
    rw [ite_eq_left hfull, Set.indicator_of_mem hx]
  · have hfull : ¬∀ i ∈ (Finset.univ : Finset (Fin m)), x i ∈ R i := by
      intro h
      exact hx ((mem_productBox R x).mpr (fun i => h i (Finset.mem_univ i)))
    rw [ite_eq_right hfull, Set.indicator_of_notMem hx]

end ReyZygmund.Geometry
