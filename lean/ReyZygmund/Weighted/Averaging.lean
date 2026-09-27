import ReyZygmund.Geometry.FiniteAverages
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # A weighted square estimate under averaging

Finite Cauchy–Schwarz and concavity give the weighted averaging inequality used
for the projected square function. Applying it to the finite partition gives the
inequality for Lebesgue averages on cubes.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry

private lemma finite_weighted_average_square {α : Type*} (s : Finset α)
    (w a b : α → ℝ) (r : ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (hws : ∑ i ∈ s, w i = 1)
    (hb : ∀ i ∈ s, 0 < b i) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (∑ i ∈ s, w i * a i) ^ 2 / Real.rpow (∑ i ∈ s, w i * b i) r ≤
      ∑ i ∈ s, w i * (a i) ^ 2 / Real.rpow (b i) r := by
  have hs : s.Nonempty := by
    apply Finset.nonempty_of_ne_empty
    intro hs
    simp [hs] at hws
  have hg : ∀ i ∈ s, 0 < w i * Real.rpow (b i) r :=
    fun i hi => mul_pos (hw i hi) (Real.rpow_pos_of_pos (hb i hi) r)
  have hsumpos : 0 < ∑ i ∈ s, w i * Real.rpow (b i) r := Finset.sum_pos hg hs
  have hmeanpos : 0 < ∑ i ∈ s, w i * b i :=
    Finset.sum_pos (fun i hi => mul_pos (hw i hi) (hb i hi)) hs
  have hmeanpow : 0 < Real.rpow (∑ i ∈ s, w i * b i) r :=
    Real.rpow_pos_of_pos hmeanpos r
  have hconc : (∑ i ∈ s, w i * Real.rpow (b i) r) ≤
      Real.rpow (∑ i ∈ s, w i * b i) r := by
    simpa only [smul_eq_mul, Real.rpow_eq_pow] using
      (Real.concaveOn_rpow hr0 hr1).le_map_sum (t := s) (w := w) (p := b)
        (fun i hi => (hw i hi).le) hws (fun i hi => (hb i hi).le)
  calc
    _ ≤ (∑ i ∈ s, w i * a i) ^ 2 / (∑ i ∈ s, w i * Real.rpow (b i) r) := by
      apply (div_le_div_iff₀ hmeanpow hsumpos).mpr
      exact mul_le_mul_of_nonneg_left hconc (sq_nonneg _)
    _ ≤ ∑ i ∈ s, (w i * a i) ^ 2 / (w i * Real.rpow (b i) r) :=
      Finset.sq_sum_div_le_sum_sq_div s (fun i => w i * a i) hg
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      field_simp [ne_of_gt (hw i hi), ne_of_gt (Real.rpow_pos_of_pos (hb i hi) r)]

variable {d : ℕ}

private lemma sum_integral_partition {I : Box (Fin d)} (π : Prepartition I)
    (hπ : π.IsPartition) (g : (Fin d → ℝ) → ℝ)
    (hg : IntegrableOn g (I : Set (Fin d → ℝ)) volume) :
    (∑ Q ∈ π.boxes, ∫ x in (Q : Set (Fin d → ℝ)), g x) =
      ∫ x in (I : Set (Fin d → ℝ)), g x := by
  rw [← hπ.iUnion_eq, Prepartition.iUnion_def]
  exact (integral_biUnion_finset π.boxes
    (fun Q _ => Q.measurableSet_coe) π.pairwiseDisjoint
    (fun Q hQ => hg.mono_set (π.le_of_mem hQ))).symm

private lemma sum_leaf_weights (I : Box (Fin d)) (N : ℕ) :
    (∑ Q ∈ leaves I N,
      volume.real (Q : Set (Fin d → ℝ)) / volume.real (I : Set (Fin d → ℝ))) = 1 := by
  have hs : (∑ Q ∈ leaves I N, volume.real (Q : Set (Fin d → ℝ))) =
      volume.real (I : Set (Fin d → ℝ)) := by
    simpa only [leaves, (level_isPartition I N).iUnion_eq] using
      ((level I N).measure_iUnion_toReal volume).symm
  rw [← Finset.sum_div, hs, div_self (ne_of_gt (box_volume_pos I))]

private lemma normalized_integral_eq_leaf_sum (I : Box (Fin d)) (N : ℕ)
    (g : (Fin d → ℝ) → ℝ)
    (hg : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y) :
    (∫ x in (I : Set (Fin d → ℝ)), g x) / volume.real (I : Set (Fin d → ℝ)) =
      ∑ Q ∈ leaves I N,
        (volume.real (Q : Set (Fin d → ℝ)) / volume.real (I : Set (Fin d → ℝ))) *
          g Q.upper := by
  rw [← sum_integral_partition (level I N) (level_isPartition I N) g
    (integrableOn_of_leafConstant I N g hg), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro Q hQ
  have hconst : (∫ x in (Q : Set (Fin d → ℝ)), g x) =
      volume.real (Q : Set (Fin d → ℝ)) * g Q.upper := by
    calc
      _ = ∫ _ in (Q : Set (Fin d → ℝ)), g Q.upper :=
        setIntegral_congr_fun Q.measurableSet_coe
          (fun x hx => hg Q hQ x hx Q.upper Q.upper_mem)
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  rw [hconst]
  ring

/-- The normalized averaging inequality for the projected square function. Constancy
on the smallest cubes gives integrability of the Lebesgue integrals. The numerator
`u` may be signed, and `p = 2` is included. -/
theorem box_average_weighted_square {d : ℕ}
    (I : Box (Fin d)) (N : ℕ)
    (u v : (Fin d → ℝ) → ℝ) (p : ℝ)
    (hp : 1 < p) (hp2 : p ≤ 2)
    (hu : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, u x = u y)
    (hv : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, v x = v y)
    (hvpos : ∀ x ∈ I, 0 < v x) :
    (((∫ x in (I : Set (Fin d → ℝ)), u x) /
        volume.real (I : Set (Fin d → ℝ))) ^ (2 : ℕ)) /
      Real.rpow
        ((∫ x in (I : Set (Fin d → ℝ)), v x) /
          volume.real (I : Set (Fin d → ℝ))) (2 - p) ≤
      (∫ x in (I : Set (Fin d → ℝ)),
        (u x) ^ (2 : ℕ) / Real.rpow (v x) (2 - p)) /
          volume.real (I : Set (Fin d → ℝ)) := by
  have henergy : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q,
      (u x) ^ 2 / Real.rpow (v x) (2 - p) =
        (u y) ^ 2 / Real.rpow (v y) (2 - p) := by
    intro Q hQ x hx y hy
    rw [hu Q hQ x hx y hy, hv Q hQ x hx y hy]
  rw [normalized_integral_eq_leaf_sum I N u hu,
    normalized_integral_eq_leaf_sum I N v hv,
    normalized_integral_eq_leaf_sum I N
      (fun x => (u x) ^ 2 / Real.rpow (v x) (2 - p)) henergy]
  calc
    _ ≤ ∑ Q ∈ leaves I N,
        (volume.real (Q : Set (Fin d → ℝ)) / volume.real (I : Set (Fin d → ℝ))) *
          (u Q.upper) ^ 2 / Real.rpow (v Q.upper) (2 - p) :=
      finite_weighted_average_square (leaves I N)
        (fun Q => volume.real (Q : Set (Fin d → ℝ)) / volume.real (I : Set (Fin d → ℝ)))
        (fun Q => u Q.upper) (fun Q => v Q.upper) (2 - p)
        (fun Q _ => div_pos (box_volume_pos Q) (box_volume_pos I))
        (sum_leaf_weights I N)
        (fun Q hQ => hvpos Q.upper ((level I N).le_of_mem hQ Q.upper_mem))
        (sub_nonneg.mpr hp2) (by linarith)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro Q _
      ring

end ReyZygmund
