import ReyZygmund.Sharpness.Generations
import ReyZygmund.Sharpness.NestedRetention

/-! # Retained cube families in each coordinate

With `m = n + 3`, the index `i : Fin (n + 2)` represents coordinates `2,…,m`.
Apply the nested retention construction at the prescribed generations. Conversions
to natural depths account for the last coordinate's initial offset.

-/

open BoxIntegral MeasureTheory
open scoped Classical

namespace ReyZygmund.Sharpness

open Geometry

private theorem selectionScale_nonneg {n N : ℕ} (hN : 2 ≤ N)
    (i : Fin (n + 2)) (k : ℕ) : 0 ≤ selectionScale N i k := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [selectionScale, Fin.cons_zero]
    positivity
  · refine Fin.lastCases ?_ (fun l => ?_) j
    · simp only [selectionScale, Fin.cons_succ, Fin.snoc_last]
      apply add_nonneg _ (Int.natCast_nonneg k)
      unfold sharpL
      have hN' : (2 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
      exact mul_nonneg (by positivity) (by omega)
    · simp only [selectionScale, Fin.cons_succ, Fin.snoc_castSucc]
      exact Int.natCast_nonneg k

/-- The paper's schedule is preserved exactly by conversion to a natural depth. -/
theorem selectionScale_toNat_cast {n N : ℕ} (hN : 2 ≤ N)
    (i : Fin (n + 2)) (k : ℕ) :
    ((selectionScale N i k).toNat : ℤ) = selectionScale N i k := by
  have h := selectionScale_nonneg hN i k
  omega

private theorem selectionScale_toNat_step {n N : ℕ} (hN : 2 ≤ N)
    (i : Fin (n + 2)) (k : ℕ) :
    (selectionScale N i k).toNat + 1 ≤ (selectionScale N i (k + 1)).toNat := by
  have h := selectionScale_step hN i k
  have hk := selectionScale_toNat_cast hN i k
  have hk1 := selectionScale_toNat_cast hN i (k + 1)
  omega

private theorem selectionScale_next_generation_cast {n N : ℕ} (hN : 2 ≤ N)
    (s : ℕ) (i : Fin (n + 2)) (k : ℕ) :
    ((s * ((selectionScale N i (k + 1)).toNat - 1) : ℕ) : ℤ) =
      (s : ℤ) * (selectionScale N i (k + 1) - 1) := by
  rw [Nat.cast_mul]
  congr 1
  have hstep := selectionScale_toNat_step hN i k
  have hcast := selectionScale_toNat_cast hN i (k + 1)
  omega

/-- Retained families for coordinates `2,…,m`. The final identity gives the measure
fraction of the disjoint subsets used to prove sparseness. -/
theorem exists_coordinate_retention (n N s : ℕ) (hN : 2 ≤ N)
    (d : Fin (n + 2) → ℕ) (hd : ∀ i, 0 < d i)
    (D : ∀ i, DyadicGrid (d i)) (Q : ∀ i, Box (Fin (d i)))
    (hQ : ∀ i, Q i ∈ (D i).cubes 0) :
    ∃ P : ∀ i, ℕ → Finset (Box (Fin (d i))),
      (∀ i, P i 0 = (level (Q i) (s * (selectionScale N i 0).toNat)).boxes) ∧
      (∀ i, boxUnion (P i 0) = (Q i : Set (Fin (d i) → ℝ))) ∧
      (∀ i k R, R ∈ P i k →
        R ∈ (D i).cubes ((s : ℤ) * selectionScale N i k)) ∧
      (∀ i k, Set.PairwiseDisjoint (↑(P i k) : Set (Box (Fin (d i))))
        (fun R => (R : Set (Fin (d i) → ℝ)))) ∧
      (∀ i k, boxUnion (P i (k + 1)) ⊆ boxUnion (P i k)) ∧
      (∀ i k, MeasurableSet (boxUnion (P i k)) ∧ volume (boxUnion (P i k)) < ⊤) ∧
      (∀ i k, volume.real (boxUnion (P i k)) =
        ((2 : ℝ) ^ (-(s : ℤ))) ^ k * volume.real (Q i : Set (Fin (d i) → ℝ))) ∧
      (∀ (a : Fin (n + 2) → Fin N) i (I : Box (Fin (d i))),
        I ∈ (D i).cubes (sharpGeneration s a i.succ) →
        (I : Set (Fin (d i) → ℝ)) ⊆ boxUnion (P i (a i).val) →
        volume.real ((I : Set (Fin (d i) → ℝ)) ∩ boxUnion (P i ((a i).val + 1))) =
          (2 : ℝ) ^ (-(s : ℤ)) * volume.real (I : Set (Fin (d i) → ℝ))) := by
  have hcoord (i : Fin (n + 2)) :=
    exists_nested_retention (hd i) (D i) (Q i) (hQ i) s
      (fun k => (selectionScale N i k).toNat) (selectionScale_toNat_step hN i)
  choose P hinit hzero hgen hdis hnest hmeas hmass hlocal using hcoord
  refine ⟨P, hinit, hzero, ?_, hdis, hnest, hmeas, hmass, ?_⟩
  · intro i k R hR
    simpa only [Nat.cast_mul, selectionScale_toNat_cast hN i k] using hgen i k R hR
  · intro a i I hI hsub
    have hbound : sharpGeneration s a i.succ ≤
        ((s * ((selectionScale N i ((a i).val + 1)).toNat - 1) : ℕ) : ℤ) := by
      rw [selectionScale_next_generation_cast hN s i (a i).val]
      exact (sharpGeneration_selection_scaled s a i).2
    have h := hlocal i (a i).val (sharpGeneration s a i.succ) hbound I hI
    rw [Set.inter_eq_left.mpr hsub] at h
    exact h

end ReyZygmund.Sharpness
