import ReyZygmund.Overlap.Countable

/-! # Finite families in the extended overlap notation -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Overlap

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

theorem shadow_finset (G : Finset (∀ i, Box (Fin (d i)))) :
    shadow (↑G) = finiteShadow G := rfl

/-- The extended overlap of a finite family equals its finite sum;
there is no infinite real sum or lost multiplicity. -/
theorem overlap_finset (G : Finset (∀ i, Box (Fin (d i))))
    (x : Fin (∑ i, d i) → ℝ) :
    overlap (↑G) x = ENNReal.ofReal (finiteOverlap G x) := by
  rw [overlap, tsum_fintype]
  rw [Finset.sum_finset_coe (fun Q : ∀ i, Box (Fin (d i)) =>
    (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)).indicator
      (fun _ => (1 : ℝ≥0∞)) x) G, finiteOverlap,
    ENNReal.ofReal_sum_of_nonneg (fun Q _ =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) x)]
  apply Finset.sum_congr rfl
  intro Q _
  by_cases hx : x ∈ (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ))
  · simp only [Set.indicator_of_mem hx, ENNReal.ofReal_one]
  · simp only [Set.indicator_of_notMem hx, ENNReal.ofReal_zero]

theorem toReal_overlap_finset (G : Finset (∀ i, Box (Fin (d i))))
    (x : Fin (∑ i, d i) → ℝ) :
    (overlap (↑G) x).toReal = finiteOverlap G x := by
  rw [overlap_finset, ENNReal.toReal_ofReal (finiteOverlap_nonneg G x)]

end ReyZygmund.Overlap
