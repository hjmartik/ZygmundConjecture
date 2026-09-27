import ReyZygmund.Maximal.Euclidean
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FieldSimp

/-! # Removing the bounded part before endpoint interpolation

A rectangle with average above a level still has average above half that level
after removing input values below half the level. Local integrability justifies
the averages. The full maximal function need not be bounded.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry

private theorem average_le_half_add_tail {k : ℕ} (Q : Box (Fin k))
    (f : (Fin k → ℝ) → ℝ) (hf : LocallyIntegrable f volume)
    (hm : Measurable f) (hn : ∀ x, 0 ≤ f x) (lam : ℝ) (hlam : 0 < lam) :
    (∫ x in (Q : Set (Fin k → ℝ)), |f x|) / volume.real (Q : Set (Fin k → ℝ)) ≤
      lam / 2 +
        (∫ x in (Q : Set (Fin k → ℝ)),
          |({y | lam / 2 < f y}.indicator f) x|) /
            volume.real (Q : Set (Fin k → ℝ)) := by
  let g := {y | lam / 2 < f y}.indicator f
  have hg0 (x) : 0 ≤ g x := Set.indicator_nonneg (fun y _ => hn y) x
  have hfl : IntegrableOn f (Q : Set (Fin k → ℝ)) volume :=
    (hf.integrableOn_isCompact Q.isCompact_Icc).mono_set Box.coe_subset_Icc
  have hgl : IntegrableOn g (Q : Set (Fin k → ℝ)) volume :=
    hfl.indicator (measurableSet_lt measurable_const hm)
  let : IsFiniteMeasure (volume.restrict (Q : Set (Fin k → ℝ))) :=
    isFiniteMeasure_restrict.mpr (Q.measure_coe_lt_top volume).ne
  have hpoint (x) : f x ≤ lam / 2 + g x := by
    by_cases hx : lam / 2 < f x
    · simp only [g, Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hx]
      linarith
    · simp only [g, Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hx, add_zero]
      exact le_of_not_gt hx
  have hint := integral_mono hfl ((integrable_const (lam / 2)).add hgl) hpoint
  change (∫ x in (Q : Set (Fin k → ℝ)), f x) ≤
    ∫ x in (Q : Set (Fin k → ℝ)), lam / 2 + g x at hint
  rw [integral_add (integrable_const (lam / 2)) hgl, setIntegral_const,
    smul_eq_mul] at hint
  have hv := box_volume_pos Q
  have hd := div_le_div_of_nonneg_right hint hv.le
  have hcancel :
      (volume.real (Q : Set (Fin k → ℝ)) * (lam / 2) +
        ∫ x in (Q : Set (Fin k → ℝ)), g x) / volume.real (Q : Set (Fin k → ℝ)) =
      lam / 2 + (∫ x in (Q : Set (Fin k → ℝ)), g x) /
        volume.real (Q : Set (Fin k → ℝ)) := by
    field_simp [hv.ne']
  rw [hcancel] at hd
  simpa only [abs_of_nonneg (hn _), abs_of_nonneg (hg0 _), g] using hd

/-- A point above level lambda remains above level lambda/2 after retaining input
values above lambda/2. The family need not be finite or incomparable. -/
theorem euclidean_maximal_truncation_levelset
    {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf : LocallyIntegrable f volume)
    (hm : Measurable f) (hn : ∀ x, 0 ≤ f x) (lam : ℝ) (hlam : 0 < lam) :
    {x | ENNReal.ofReal lam < euclideanFamilyMaximal G f x} ⊆
      {x | ENNReal.ofReal (lam / 2) < euclideanFamilyMaximal G
        ({y | lam / 2 < f y}.indicator f) x} := by
  intro x hx
  change ENNReal.ofReal lam < ⨆ Q : G, ENNReal.ofReal
    ((flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)).indicator
      (fun _ => (∫ y in (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)), |f y|) /
        volume.real (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ))) x) at hx
  obtain ⟨Q, hQ⟩ := lt_iSup_iff.mp hx
  have hxQ : x ∈ (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)) := by
    by_contra hnot
    simp only [Set.indicator_of_notMem hnot, ENNReal.ofReal_zero] at hQ
    exact (not_lt_of_ge zero_le) hQ
  rw [Set.indicator_of_mem hxQ] at hQ
  have havg := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hlam.le).mp hQ
  have htail := average_le_half_add_tail (flatProductBox Q.1) f hf hm hn lam hlam
  have hstrict : lam / 2 <
      (∫ y in (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)),
        |({z | lam / 2 < f z}.indicator f) y|) /
          volume.real (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)) := by
    linarith
  change ENNReal.ofReal (lam / 2) < ⨆ Q : G, ENNReal.ofReal
    ((flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)).indicator
      (fun _ => (∫ y in (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)),
        |({z | lam / 2 < f z}.indicator f) y|) /
          volume.real (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ))) x)
  apply lt_of_lt_of_le _ (le_iSup_of_le Q le_rfl)
  rw [Set.indicator_of_mem hxQ]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr hstrict

end ReyZygmund
