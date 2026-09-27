import ReyZygmund.Maximal.FamilyProperties

/-! # Level-set estimates on the top rectangle

The measure is restricted product Lebesgue measure. Its finiteness is established
before using real-valued measures. Chebyshev's inequality assumes square
integrability, which is proved for the inputs in subsequent applications.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- Chebyshev's square estimate for the strict level set in the top rectangle. -/
theorem product_root_strict_level_le_square_integral
    (I : ∀ i, Box (Fin (d i))) (H : ProductPoint d → ℝ)
    (hH : IntegrableOn (fun x => (H x) ^ 2) (productBox I) volume)
    (t : ℝ) (ht : 0 < t) :
    (volume.restrict (productBox I)).real {x | t < H x} ≤
      (∫ x in productBox I, (H x) ^ 2) / t ^ 2 := by
  have hvol : volume (productBox I) < ∞ := by
    change Measure.pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
      (Set.pi Set.univ (fun i => (I i : Set (Fin (d i) → ℝ)))) < ∞
    rw [Measure.pi_pi]
    exact ENNReal.prod_lt_top (fun i _ => (I i).measure_coe_lt_top volume)
  let : IsFiniteMeasure (volume.restrict (productBox I)) :=
    isFiniteMeasure_restrict.mpr hvol.ne
  have hsub : {x | t < H x} ⊆ {x | t ^ 2 ≤ (H x) ^ 2} := by
    intro x hx
    change t < H x at hx
    change t ^ 2 ≤ (H x) ^ 2
    nlinarith
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x : ProductPoint d => sq_nonneg (H x))) hH (t ^ 2)
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  calc
    _ = t ^ 2 * (volume.restrict (productBox I)).real {x | t < H x} := mul_comm _ _
    _ ≤ t ^ 2 * (volume.restrict (productBox I)).real {x | t ^ 2 ≤ (H x) ^ 2} :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsub) (sq_nonneg t)
    _ ≤ _ := hm

end ReyZygmund
