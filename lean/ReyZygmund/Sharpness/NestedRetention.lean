import ReyZygmund.Sharpness.RetainedPartition
import Mathlib.Tactic.NormNum

/-! # Nested retained finite families

The prescribed scale schedule may start above zero. The initial family is the
refinement at that scale; subsequent families are constructed by
finite refinement and the proved retained-partition step.
-/

open BoxIntegral MeasureTheory
open scoped Classical

namespace ReyZygmund.Sharpness

open Geometry

private theorem exists_next_retention {d : ℕ} (hd : 0 < d) (D : DyadicGrid d)
    (s : ℕ) (b : ℕ → ℕ) (hb : ∀ k, b k + 1 ≤ b (k + 1)) (k : ℕ)
    (A : Finset (Box (Fin d)))
    (hA : ∀ R ∈ A, R ∈ D.cubes ((s * b k : ℕ) : ℤ)) :
    ∃ F : Finset (Box (Fin d)),
      (∀ R ∈ F, R ∈ D.cubes ((s * b (k + 1) : ℕ) : ℤ)) ∧
      boxUnion F ⊆ boxUnion A ∧
      volume.real (boxUnion F) = (2 : ℝ) ^ (-(s : ℤ)) * volume.real (boxUnion A) ∧
      ∀ (n : ℤ), n ≤ ((s * (b (k + 1) - 1) : ℕ) : ℤ) → ∀ I ∈ D.cubes n,
        volume.real ((I : Set (Fin d → ℝ)) ∩ boxUnion F) =
          (2 : ℝ) ^ (-(s : ℤ)) * volume.real ((I : Set (Fin d → ℝ)) ∩ boxUnion A) := by
  have hbk : b k ≤ b (k + 1) - 1 := by have h := hb k; omega
  have hpred : b (k + 1) - 1 + 1 = b (k + 1) := by have h := hb k; omega
  let t : ℕ := s * ((b (k + 1) - 1) - b k)
  have href : s * b k + t = s * (b (k + 1) - 1) := by
    dsimp only [t]
    rw [← Nat.mul_add, Nat.add_sub_of_le hbk]
  have hrefZ : ((s * b k : ℕ) : ℤ) + (t : ℤ) =
      ((s * (b (k + 1) - 1) : ℕ) : ℤ) := by exact_mod_cast href
  have hnext : s * (b (k + 1) - 1) + s = s * b (k + 1) := by
    calc
      _ = s * (b (k + 1) - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [hpred]
  have hnextZ : ((s * (b (k + 1) - 1) : ℕ) : ℤ) + (s : ℤ) =
      ((s * b (k + 1) : ℕ) : ℤ) := by exact_mod_cast hnext
  let R : Finset (Box (Fin d)) := A.biUnion (fun Q => (level Q t).boxes)
  have hR (Q : Box (Fin d)) (hQ : Q ∈ R) :
      Q ∈ D.cubes ((s * (b (k + 1) - 1) : ℕ) : ℤ) := by
    obtain ⟨J, hJ, hQJ⟩ := Finset.mem_biUnion.mp hQ
    have h := D.mem_cubes_of_mem_level (hA J hJ) hQJ
    simpa only [hrefZ] using h
  have hRunion : boxUnion R = boxUnion A := boxUnion_level_biUnion A t
  obtain ⟨F, _, hF, _, hsub, _, _, hmass, hlocal⟩ :=
    exists_retained_partition hd D ((s * (b (k + 1) - 1) : ℕ) : ℤ) R hR s
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro Q hQ
    simpa only [hnextZ] using hF Q hQ
  · simpa only [hRunion] using hsub
  · simpa only [hRunion] using hmass
  · intro n hn I hI
    simpa only [hRunion] using hlocal n hn I hI

/-- A nested sequence at the prescribed scales. The initial family may have positive
offset b0, but its union is the top cube. -/
theorem exists_nested_retention {d : ℕ} (hd : 0 < d) (D : DyadicGrid d)
    (Q : Box (Fin d)) (hQ : Q ∈ D.cubes 0) (s : ℕ) (b : ℕ → ℕ)
    (hb : ∀ k, b k + 1 ≤ b (k + 1)) :
    ∃ P : ℕ → Finset (Box (Fin d)),
      P 0 = (level Q (s * b 0)).boxes ∧
      boxUnion (P 0) = (Q : Set (Fin d → ℝ)) ∧
      (∀ k R, R ∈ P k → R ∈ D.cubes ((s * b k : ℕ) : ℤ)) ∧
      (∀ k, Set.PairwiseDisjoint (↑(P k) : Set (Box (Fin d)))
        (fun R => (R : Set (Fin d → ℝ)))) ∧
      (∀ k, boxUnion (P (k + 1)) ⊆ boxUnion (P k)) ∧
      (∀ k, MeasurableSet (boxUnion (P k)) ∧ volume (boxUnion (P k)) < ⊤) ∧
      (∀ k, volume.real (boxUnion (P k)) =
        ((2 : ℝ) ^ (-(s : ℤ))) ^ k * volume.real (Q : Set (Fin d → ℝ))) ∧
      (∀ k (n : ℤ), n ≤ ((s * (b (k + 1) - 1) : ℕ) : ℤ) → ∀ I ∈ D.cubes n,
        volume.real ((I : Set (Fin d → ℝ)) ∩ boxUnion (P (k + 1))) =
          (2 : ℝ) ^ (-(s : ℤ)) *
            volume.real ((I : Set (Fin d → ℝ)) ∩ boxUnion (P k))) := by
  let Stage (k : ℕ) :=
    {A : Finset (Box (Fin d)) // ∀ R ∈ A, R ∈ D.cubes ((s * b k : ℕ) : ℤ)}
  let initial : Stage 0 := ⟨(level Q (s * b 0)).boxes, by
    intro R hR
    simpa only [zero_add] using D.mem_cubes_of_mem_level hQ hR⟩
  let step (k : ℕ) (A : Stage k) : Stage (k + 1) :=
    ⟨Classical.choose (exists_next_retention hd D s b hb k A.1 A.2),
      (Classical.choose_spec (exists_next_retention hd D s b hb k A.1 A.2)).1⟩
  let S : ∀ k, Stage k := Nat.rec initial step
  let P (k : ℕ) : Finset (Box (Fin d)) := (S k).1
  have hzero : P 0 = (level Q (s * b 0)).boxes := rfl
  have hzeroUnion : boxUnion (P 0) = (Q : Set (Fin d → ℝ)) := by
    rw [hzero]
    change (level Q (s * b 0)).iUnion = _
    exact (level_isPartition Q (s * b 0)).iUnion_eq
  have hgen (k : ℕ) (R : Box (Fin d)) (hR : R ∈ P k) :
      R ∈ D.cubes ((s * b k : ℕ) : ℤ) := (S k).2 R hR
  have hstep (k : ℕ) :
      boxUnion (P (k + 1)) ⊆ boxUnion (P k) ∧
      volume.real (boxUnion (P (k + 1))) =
        (2 : ℝ) ^ (-(s : ℤ)) * volume.real (boxUnion (P k)) ∧
      ∀ (n : ℤ), n ≤ ((s * (b (k + 1) - 1) : ℕ) : ℤ) → ∀ I ∈ D.cubes n,
        volume.real ((I : Set (Fin d → ℝ)) ∩ boxUnion (P (k + 1))) =
          (2 : ℝ) ^ (-(s : ℤ)) *
            volume.real ((I : Set (Fin d → ℝ)) ∩ boxUnion (P k)) := by
    exact (Classical.choose_spec
      (exists_next_retention hd D s b hb k (S k).1 (S k).2)).2
  have hdis (k : ℕ) : Set.PairwiseDisjoint (↑(P k) : Set (Box (Fin d)))
      (fun R => (R : Set (Fin d → ℝ))) := by
    intro R hR T hT hne
    exact D.disjoint _ (hgen k R hR) (hgen k T hT) hne
  have hmass (k : ℕ) : volume.real (boxUnion (P k)) =
      ((2 : ℝ) ^ (-(s : ℤ))) ^ k * volume.real (Q : Set (Fin d → ℝ)) := by
    induction k with
    | zero => rw [hzeroUnion]; simp
    | succ k ih =>
      rw [(hstep k).2.1, ih, pow_succ']
      exact (mul_assoc _ _ _).symm
  exact ⟨P, hzero, hzeroUnion, hgen, hdis, fun k => (hstep k).1,
    fun k => ⟨measurableSet_boxUnion (P k), volume_boxUnion_lt_top (P k)⟩,
    hmass, fun k => (hstep k).2.2⟩

end ReyZygmund.Sharpness
