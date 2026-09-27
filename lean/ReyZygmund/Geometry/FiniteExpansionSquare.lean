import ReyZygmund.Geometry.RawDifferenceSteps
import ReyZygmund.Geometry.GridFiniteExpansion
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # The square function of a finite difference expansion

All positive power integrals of this finite square function are finite.
Orthogonality identifies it with the square function indexed by the entire grid.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

noncomputable def finiteDifferenceSquare
    (H : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ)
    (x : ProductPoint d) : ℝ :=
  Real.sqrt (∑ Q ∈ H, (rawProductDifference Q f x) ^ 2)

theorem measurable_finiteDifferenceSquare
    (H : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ) :
    Measurable (finiteDifferenceSquare H f) :=
  Real.continuous_sqrt.measurable.comp
    (Finset.measurable_sum H (fun Q _ => (measurable_rawProductDifference Q f).pow_const 2))

theorem finiteDifferenceSquare_eq_zero_off
    (H : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ)
    (x : ProductPoint d) (hx : ∀ Q ∈ H, x ∉ productBox Q) :
    finiteDifferenceSquare H f x = 0 := by
  have hz : ∑ Q ∈ H, (rawProductDifference Q f x) ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro Q hQ
    rw [rawProductDifference_eq_zero_of_notMem Q f x (hx Q hQ), zero_pow (by decide : 2 ≠ 0)]
  simp only [finiteDifferenceSquare, hz, Real.sqrt_zero]

theorem bounded_finiteDifferenceSquare
    (H : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, finiteDifferenceSquare H f x ≤ C := by
  choose C hC0 hC using fun Q => bounded_rawProductDifference Q f
  refine ⟨Real.sqrt (∑ Q ∈ H, (C Q) ^ 2), Real.sqrt_nonneg _, ?_⟩
  intro x
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro Q _
  have hh := pow_le_pow_left₀ (abs_nonneg (rawProductDifference Q f x)) (hC Q x) 2
  simpa only [sq_abs] using hh

theorem integrable_rpow_finiteDifferenceSquare
    (H : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ)
    (p : ℝ) (hp : 0 < p) :
    Integrable (fun x => Real.rpow (finiteDifferenceSquare H f x) p) volume := by
  let U : Set (ProductPoint d) := ⋃ Q ∈ H, productBox Q
  have hmU : MeasurableSet U := MeasurableSet.biUnion H.countable_toSet
    (fun Q _ => measurableSet_productBox Q)
  have hU : volume U < ∞ := measure_biUnion_lt_top H.finite_toSet
    (fun Q _ => productBox_volume_lt_top Q)
  obtain ⟨C, hC0, hC⟩ := bounded_finiteDifferenceSquare H f
  have hi : IntegrableOn (fun x => Real.rpow (finiteDifferenceSquare H f x) p) U volume := by
    apply IntegrableOn.of_bound hU
      (((Real.continuous_rpow_const hp.le).measurable.comp
        (measurable_finiteDifferenceSquare H f)).aestronglyMeasurable) (Real.rpow C p)
    apply Filter.Eventually.of_forall
    intro x
    change ‖Real.rpow (finiteDifferenceSquare H f x) p‖ ≤ Real.rpow C p
    simp only [Real.norm_eq_abs, Real.rpow_eq_pow]
    rw [abs_of_nonneg (Real.rpow_nonneg
      (show 0 ≤ finiteDifferenceSquare H f x from Real.sqrt_nonneg _) p)]
    exact Real.rpow_le_rpow (Real.sqrt_nonneg _) (hC x) hp.le
  have heq : U.indicator (fun x => Real.rpow (finiteDifferenceSquare H f x) p) =
      fun x => Real.rpow (finiteDifferenceSquare H f x) p := by
    funext x
    by_cases hx : x ∈ U
    · exact Set.indicator_of_mem hx _
    · rw [Set.indicator_of_notMem hx]
      rw [finiteDifferenceSquare_eq_zero_off H f x (by
        intro Q hQ hxQ
        exact hx (Set.mem_iUnion₂.mpr ⟨Q, hQ, hxQ⟩))]
      exact (Real.zero_rpow hp.ne').symm
  exact heq ▸ hi.integrable_indicator hmU

theorem fullGridSquare_eq_ofReal_finiteDifferenceSquare
    (D : ∀ i, DyadicGrid (d i)) (hd : ∀ i, 0 < d i)
    (H : Finset (∀ i, Box (Fin (d i)))) (hH : (↑H : Set _) ⊆ gridRectangles D)
    (F : boundedMeasurableFunctions d)
    (hex : F.1 = fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x)
    (x : ProductPoint d) :
    fullGridSquare D F.1 x = ENNReal.ofReal (finiteDifferenceSquare H F.1 x) := by
  rw [fullGridSquare_eq_finite_expansion D hd H hH F hex x]
  have hs : (∑ Q ∈ H, (ENNReal.ofReal |rawProductDifference Q F.1 x|) ^ 2) =
      ENNReal.ofReal (∑ Q ∈ H, (rawProductDifference Q F.1 x) ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun Q _ => sq_nonneg _)]
    apply Finset.sum_congr rfl
    intro Q _
    rw [← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
  rw [hs, ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg (fun Q _ => sq_nonneg _))
    (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  exact (Real.sqrt_eq_rpow _).symm

end ReyZygmund.Geometry
