import ReyZygmund.Geometry.FiniteAverages
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp

/-! # One retention step

Select a finite subfamily from a dyadic subdivision and prove its cardinality,
disjointness and Lebesgue measure. `NestedRetention.lean` iterates this step to
construct the retained sets.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Sharpness

open Geometry

/-- All depth-s descendants have the same Lebesgue volume. -/
theorem level_box_volume {d s : ℕ} {Q R : Box (Fin d)} (hR : R ∈ level Q s) :
    volume.real (R : Set (Fin d → ℝ)) =
      volume.real (Q : Set (Fin d → ℝ)) / (2 : ℝ) ^ (s * d) := by
  simp only [measureReal_def, Box.volume_apply']
  simp_rw [width_of_mem_level hR]
  rw [Finset.prod_div_distrib]
  simp [← pow_mul]

/-- The cardinality of the concrete level, obtained from its children. -/
theorem level_boxes_card {d : ℕ} (Q : Box (Fin d)) (s : ℕ) :
    (level Q s).boxes.card = 2 ^ (s * d) := by
  induction s with
  | zero => simp [level]
  | succ s ih =>
    have hcard := (level Q s).sum_biUnion_boxes Prepartition.splitCenter
      (fun _ => (1 : ℕ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hcard
    calc
      (level Q (s + 1)).boxes.card =
          ∑ R ∈ (level Q s).boxes, (Prepartition.splitCenter R).boxes.card := by
        simpa [level_succ, Prepartition.biUnion] using hcard
      _ = 2 ^ ((s + 1) * d) := by
        simp [splitCenter_card, ih, Nat.add_mul, pow_add]

/-- Retain exactly the paper's number of depth-s boxes, with fraction
`2^(-s)` of the parent's measure. The valid s=0 case retains the whole box. -/
theorem exists_retained_level {d : ℕ} (hd : 0 < d) (Q : Box (Fin d)) (s : ℕ) :
    ∃ F : Finset (Box (Fin d)),
      F ⊆ (level Q s).boxes ∧
      F.card = 2 ^ (s * (d - 1)) ∧
      Set.PairwiseDisjoint (↑F : Set (Box (Fin d))) (fun R => (R : Set (Fin d → ℝ))) ∧
      (⋃ R ∈ F, (R : Set (Fin d → ℝ))) ⊆ (Q : Set (Fin d → ℝ)) ∧
      MeasurableSet (⋃ R ∈ F, (R : Set (Fin d → ℝ))) ∧
      0 < volume.real (⋃ R ∈ F, (R : Set (Fin d → ℝ))) ∧
      volume (⋃ R ∈ F, (R : Set (Fin d → ℝ))) < ⊤ ∧
      volume.real (⋃ R ∈ F, (R : Set (Fin d → ℝ))) =
        (2 : ℝ) ^ (-(s : ℤ)) * volume.real (Q : Set (Fin d → ℝ)) := by
  have hcount : 2 ^ (s * (d - 1)) ≤ (level Q s).boxes.card := by
    rw [level_boxes_card]
    exact pow_le_pow_right' (by norm_num) (Nat.mul_le_mul_left s (by omega))
  obtain ⟨F, hF, hcard⟩ := Finset.exists_subset_card_eq hcount
  have hdis : Set.PairwiseDisjoint (↑F : Set (Box (Fin d)))
      (fun R => (R : Set (Fin d → ℝ))) := by
    intro R hR S hS hRS
    exact (level Q s).pairwiseDisjoint (hF hR) (hF hS) hRS
  have hsub : (⋃ R ∈ F, (R : Set (Fin d → ℝ))) ⊆ (Q : Set (Fin d → ℝ)) := by
    intro x hx
    obtain ⟨R, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hR, hxR⟩ := Set.mem_iUnion.mp hx
    exact (level Q s).le_of_mem (hF hR) hxR
  have hmeas : MeasurableSet (⋃ R ∈ F, (R : Set (Fin d → ℝ))) :=
    Finset.measurableSet_biUnion F (fun R _ => R.measurableSet_coe)
  have hfinite : volume (⋃ R ∈ F, (R : Set (Fin d → ℝ))) < ⊤ :=
    (measure_mono hsub).trans_lt (Q.measure_coe_lt_top volume)
  have hvol : volume.real (⋃ R ∈ F, (R : Set (Fin d → ℝ))) =
      (F.card : ℝ) * (volume.real (Q : Set (Fin d → ℝ)) / (2 : ℝ) ^ (s * d)) := by
    calc
      _ = ∑ R ∈ F, volume.real (R : Set (Fin d → ℝ)) :=
        measureReal_biUnion_finset hdis (fun R _ => R.measurableSet_coe)
          (fun R _ => (R.measure_coe_lt_top volume).ne)
      _ = ∑ _R ∈ F, volume.real (Q : Set (Fin d → ℝ)) / (2 : ℝ) ^ (s * d) :=
        Finset.sum_congr rfl (fun R hR => level_box_volume (hF hR))
      _ = _ := by simp
  have hexp : s * d = s * (d - 1) + s := by
    have hd' : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
    calc
      s * d = s * (d - 1 + 1) := by rw [hd']
      _ = s * (d - 1) + s := by rw [Nat.mul_add, Nat.mul_one]
  have hmass : volume.real (⋃ R ∈ F, (R : Set (Fin d → ℝ))) =
      (2 : ℝ) ^ (-(s : ℤ)) * volume.real (Q : Set (Fin d → ℝ)) := by
    rw [hvol, hcard]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [hexp, pow_add, zpow_neg, zpow_natCast]
    field_simp
  have hpositive : 0 < volume.real (⋃ R ∈ F, (R : Set (Fin d → ℝ))) := by
    rw [hmass]
    exact mul_pos (zpow_pos (by norm_num) _) (box_volume_pos Q)
  exact ⟨F, hF, hcard, hdis, hsub, hmeas, hpositive, hfinite, hmass⟩

end ReyZygmund.Sharpness
