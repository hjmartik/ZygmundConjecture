import ReyZygmund.Sharpness.FiniteIntegral

/-! # An integral lower bound from the maximum-overlap set -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Sharpness

open Geometry Overlap

theorem finite_overlap_exponential_lower {m : ℕ} {d : Fin m → ℕ}
    (G : Finset (∀ i, Box (Fin (d i))))
    (L : Set (Fin (∑ i, d i) → ℝ)) (hLm : MeasurableSet L)
    (hLs : L ⊆ finiteShadow G) (M c beta : ℝ)
    (hlevel : ∀ x ∈ L, finiteOverlap G x = M)
    (hc : 0 < c) (hbeta : 0 < beta) :
    volume.real L * (Real.exp (c * Real.rpow M beta) - 1) ≤
      ∫ x in finiteShadow G, Real.exp (c * Real.rpow (finiteOverlap G x) beta) - 1 := by
  have heq : (∫ x in L, Real.exp (c * Real.rpow (finiteOverlap G x) beta) - 1) =
      volume.real L * (Real.exp (c * Real.rpow M beta) - 1) := by
    calc
      _ = ∫ _x in L, Real.exp (c * Real.rpow M beta) - 1 :=
        setIntegral_congr_fun hLm (fun x hx => by rw [hlevel x hx])
      _ = _ := by simp only [integral_const, measureReal_def,
        Measure.restrict_apply_univ, smul_eq_mul]
  rw [← heq]
  exact setIntegral_mono_set (integrableOn_finite_overlap_exponential G c beta hc hbeta)
    (Filter.Eventually.of_forall (finite_overlap_exponential_nonneg G c beta hc.le))
    (Filter.Eventually.of_forall (fun _ hx => hLs hx))

end ReyZygmund.Sharpness
