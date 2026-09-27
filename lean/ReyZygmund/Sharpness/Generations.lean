import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # Generation arithmetic for the sharpness construction

There are `n + 3` coordinates. The index `a : Fin (n + 2) → Fin N` lists
`a₂,…,a_m`; when `m = 3` there are no middle coordinates. Subtraction is in the
integers, rather than truncated natural subtraction. These formulas determine the
scales used in the rectangle construction.
-/

open scoped BigOperators

namespace ReyZygmund.Sharpness

/-- The exact source value `(2*N + m - 2)*(N - 1)`, for `m = n + 3`. -/
def sharpL (n N : ℕ) : ℤ :=
  (2 * (N : ℤ) + ((n + 1 : ℕ) : ℤ)) * ((N : ℤ) - 1)

/-- The generations before multiplication by the common retention integer. -/
def generationUnits {n : ℕ} (N : ℕ) (a : Fin (n + 2) → Fin N) :
    Fin (n + 3) → ℤ :=
  Fin.cons
    (sharpL n N - 2 * (N : ℤ) * (a 0 : ℤ) -
      ∑ j : Fin (n + 1), (a j.succ : ℤ))
    (Fin.cons
      (2 * (N : ℤ) * (a 0 : ℤ) + 2 * (a (Fin.last (n + 1)) : ℤ))
      (Fin.snoc (fun j : Fin n => (a j.castSucc.succ : ℤ))
        (sharpL n N + (a (Fin.last (n + 1)) : ℤ))))

/-- Source `n_i(a)`, with the exact common integer factor `s`. -/
def sharpGeneration {n N : ℕ} (s : ℕ) (a : Fin (n + 2) → Fin N)
    (i : Fin (n + 3)) : ℤ := (s : ℤ) * generationUnits N a i

/-- Source `b_i(k)` for coordinates `i = 2,…,m`; in particular the last
coordinate has `b_m(0) = L`, not zero. -/
def selectionScale {n : ℕ} (N : ℕ) (i : Fin (n + 2)) (k : ℕ) : ℤ :=
  (Fin.cons (2 * (N : ℤ) * (k : ℤ))
    (Fin.snoc (fun _ : Fin n => (k : ℤ)) (sharpL n N + (k : ℤ))) :
      Fin (n + 2) → ℤ) i

private theorem index_bounds {n N : ℕ} (a : Fin (n + 2) → Fin N)
    (i : Fin (n + 2)) : 0 ≤ (a i : ℤ) ∧ (a i : ℤ) ≤ (N : ℤ) - 1 := by
  have hi : ((a i).val : ℤ) < (N : ℤ) := by exact_mod_cast (a i).isLt
  exact ⟨Int.natCast_nonneg _, by omega⟩

private theorem sharpL_nonneg (n N : ℕ) (hN : 2 ≤ N) : 0 ≤ sharpL n N := by
  have hN' : (2 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  unfold sharpL
  exact mul_nonneg (by positivity) (by omega)

private theorem index_weight_le {n N : ℕ} (a : Fin (n + 2) → Fin N) :
    2 * (N : ℤ) * (a 0 : ℤ) + (∑ j : Fin (n + 1), (a j.succ : ℤ)) ≤
      sharpL n N := by
  have hsum : (∑ j : Fin (n + 1), (a j.succ : ℤ)) ≤
      ((n + 1 : ℕ) : ℤ) * ((N : ℤ) - 1) := by
    calc
      _ ≤ ∑ _j : Fin (n + 1), ((N : ℤ) - 1) :=
        Finset.sum_le_sum (fun j _ => (index_bounds a j.succ).2)
      _ = _ := by simp; ring
  have hfirst := mul_le_mul_of_nonneg_left (index_bounds a 0).2
    (show 0 ≤ 2 * (N : ℤ) by positivity)
  unfold sharpL
  nlinarith

private theorem generationUnits_nonneg {n N : ℕ} (hN : 2 ≤ N)
    (a : Fin (n + 2) → Fin N) (i : Fin (n + 3)) :
    0 ≤ generationUnits N a i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [generationUnits, Fin.cons_zero]
    have h := index_weight_le a
    omega
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp only [generationUnits, Fin.cons_succ, Fin.cons_zero]
      positivity
    · refine Fin.lastCases ?_ (fun l => ?_) k
      · simp only [generationUnits, Fin.cons_succ, Fin.snoc_last]
        exact add_nonneg (sharpL_nonneg n N hN) (index_bounds a _).1
      · simpa only [generationUnits, Fin.cons_succ, Fin.snoc_castSucc] using
          (index_bounds a l.castSucc.succ).1

/-- All integer generations are nonnegative, with no truncation in
the defining first-coordinate subtraction. -/
theorem sharpGeneration_nonneg {n N : ℕ} (hN : 2 ≤ N) (s : ℕ)
    (a : Fin (n + 2) → Fin N) (i : Fin (n + 3)) :
    0 ≤ sharpGeneration s a i :=
  mul_nonneg (Int.natCast_nonneg s) (generationUnits_nonneg hN a i)

private theorem generationUnits_last {n N : ℕ} (a : Fin (n + 2) → Fin N) :
    generationUnits N a (Fin.last (n + 2)) =
      sharpL n N + (a (Fin.last (n + 1)) : ℤ) := by
  change generationUnits N a (Fin.last n).succ.succ = _
  simp only [generationUnits, Fin.cons_succ, Fin.snoc_last]

/-- The exact classical Zygmund relation among the generations. -/
theorem sharpGeneration_sum {n N : ℕ} (s : ℕ) (a : Fin (n + 2) → Fin N) :
    sharpGeneration s a (Fin.last (n + 2)) =
      ∑ i : Fin (n + 2), sharpGeneration s a i.castSucc := by
  simp only [sharpGeneration]
  rw [← Finset.mul_sum]
  congr 1
  rw [generationUnits_last, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, Fin.castSucc_succ, generationUnits,
    Fin.cons_zero, Fin.cons_succ, Fin.snoc_castSucc]
  rw [Fin.sum_univ_castSucc (fun j : Fin (n + 1) => (a j.succ : ℤ))]
  simp only [Fin.succ_last]
  ring

/-- Coordinatewise domination of the generations forces identical
indices. This is the arithmetic needed for spatial incomparability. -/
theorem sharpGeneration_eq_of_ge {n N s : ℕ} (hN : 2 ≤ N) (hs : 1 ≤ s)
    (a a' : Fin (n + 2) → Fin N)
    (hdom : ∀ i, sharpGeneration s a' i ≤ sharpGeneration s a i) : a = a' := by
  have hs' : (0 : ℤ) < (s : ℤ) := by omega
  have hN' : (2 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have hu (i : Fin (n + 3)) : generationUnits N a' i ≤ generationUnits N a i := by
    exact (mul_le_mul_iff_right₀ hs').mp (hdom i)
  have htail (j : Fin (n + 1)) : (a' j.succ : ℤ) ≤ (a j.succ : ℤ) := by
    refine Fin.lastCases ?_ (fun k => ?_) j
    · have h := hu (Fin.last (n + 2))
      rw [generationUnits_last, generationUnits_last] at h
      simpa only [Fin.succ_last] using
        (show (a' (Fin.last (n + 1)) : ℤ) ≤ (a (Fin.last (n + 1)) : ℤ) by omega)
    · simpa only [generationUnits, Fin.cons_succ, Fin.snoc_castSucc] using
        hu k.castSucc.succ.succ
  have hsecond :
      2 * (N : ℤ) * (a' 0 : ℤ) + 2 * (a' (Fin.last (n + 1)) : ℤ) ≤
        2 * (N : ℤ) * (a 0 : ℤ) + 2 * (a (Fin.last (n + 1)) : ℤ) := by
    simpa only [generationUnits, Fin.cons_succ, Fin.cons_zero] using
      hu (0 : Fin (n + 2)).succ
  have hzero_le : (a' 0 : ℤ) ≤ (a 0 : ℤ) := by
    by_contra h
    have hgap : (a 0 : ℤ) + 1 ≤ (a' 0 : ℤ) := by omega
    have hgapmul := mul_le_mul_of_nonneg_left hgap
      (show 0 ≤ 2 * (N : ℤ) by positivity)
    have hlast := (index_bounds a (Fin.last (n + 1))).2
    have hlast' := (index_bounds a' (Fin.last (n + 1))).1
    nlinarith
  have hsum_le : (∑ j : Fin (n + 1), (a' j.succ : ℤ)) ≤
      ∑ j : Fin (n + 1), (a j.succ : ℤ) :=
    Finset.sum_le_sum (fun j _ => htail j)
  have hfirst :
      sharpL n N - 2 * (N : ℤ) * (a' 0 : ℤ) -
          (∑ j : Fin (n + 1), (a' j.succ : ℤ)) ≤
        sharpL n N - 2 * (N : ℤ) * (a 0 : ℤ) -
          (∑ j : Fin (n + 1), (a j.succ : ℤ)) := by
    simpa only [generationUnits, Fin.cons_zero] using hu 0
  have hmul_le : 2 * (N : ℤ) * (a 0 : ℤ) ≤ 2 * (N : ℤ) * (a' 0 : ℤ) := by
    linarith
  have hzero : (a 0 : ℤ) = (a' 0 : ℤ) :=
    le_antisymm ((mul_le_mul_iff_right₀ (show 0 < 2 * (N : ℤ) by omega)).mp hmul_le)
      hzero_le
  have hsum_eq : (∑ j : Fin (n + 1), (a' j.succ : ℤ)) =
      ∑ j : Fin (n + 1), (a j.succ : ℤ) := by
    rw [hzero] at hfirst
    omega
  have htail_eq := (Finset.sum_eq_sum_iff_of_le
    (s := Finset.univ) (f := fun j : Fin (n + 1) => (a' j.succ : ℤ))
    (g := fun j : Fin (n + 1) => (a j.succ : ℤ)) (fun j _ => htail j)).mp hsum_eq
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · apply Fin.ext
    exact_mod_cast hzero
  · apply Fin.ext
    exact_mod_cast (htail_eq j (Finset.mem_univ j)).symm

/-- The first partition scale is at least one in every retained coordinate. -/
theorem selectionScale_one {n N : ℕ} (hN : 2 ≤ N) (i : Fin (n + 2)) :
    1 ≤ selectionScale N i 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [selectionScale, Fin.cons_zero, Nat.cast_one, mul_one]
    have hN' : (2 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    omega
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [selectionScale, Fin.cons_succ, Fin.snoc_last, Nat.cast_one]
      have h := sharpL_nonneg n N hN
      omega
    · simp only [selectionScale, Fin.cons_succ, Fin.snoc_castSucc, Nat.cast_one, le_refl]

/-- Every subsequent partition scale refines the previous retained scale. -/
theorem selectionScale_step {n N : ℕ} (hN : 2 ≤ N) (i : Fin (n + 2)) (k : ℕ) :
    selectionScale N i k ≤ selectionScale N i (k + 1) - 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [selectionScale, Fin.cons_zero, Nat.cast_add, Nat.cast_one]
    have hN' : (2 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    nlinarith
  · refine Fin.lastCases ?_ (fun l => ?_) j
    · simp [selectionScale]
      omega
    · simp [selectionScale]

private theorem generationUnits_selection {n N : ℕ}
    (a : Fin (n + 2) → Fin N) (i : Fin (n + 2)) :
    selectionScale N i (a i).val ≤ generationUnits N a i.succ ∧
      generationUnits N a i.succ ≤ selectionScale N i ((a i).val + 1) - 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [selectionScale, generationUnits, Fin.cons_zero, Fin.cons_succ,
      Nat.cast_add, Nat.cast_one]
    have hlast := index_bounds a (Fin.last (n + 1))
    constructor <;> nlinarith
  · refine Fin.lastCases ?_ (fun l => ?_) j
    · simp [selectionScale, generationUnits]
      omega
    · simp [selectionScale, generationUnits]

/-- Division-free selection scales, ready for dyadic refinements. -/
theorem sharpGeneration_selection_scaled {n N : ℕ} (s : ℕ)
    (a : Fin (n + 2) → Fin N) (i : Fin (n + 2)) :
    (s : ℤ) * selectionScale N i (a i).val ≤ sharpGeneration s a i.succ ∧
      sharpGeneration s a i.succ ≤
        (s : ℤ) * (selectionScale N i ((a i).val + 1) - 1) := by
  obtain ⟨hlo, hhi⟩ := generationUnits_selection a i
  exact ⟨mul_le_mul_of_nonneg_left hlo (Int.natCast_nonneg s),
    mul_le_mul_of_nonneg_left hhi (Int.natCast_nonneg s)⟩

private theorem generation_quotient {n N : ℕ} {s : ℕ} (hs : 1 ≤ s)
    (a : Fin (n + 2) → Fin N) (i : Fin (n + 3)) :
    sharpGeneration s a i / (s : ℤ) = generationUnits N a i := by
  have hs' : (s : ℤ) ≠ 0 := by omega
  exact Int.mul_ediv_cancel_left _ hs'

/-- The paper's exact quotient-form selection inequalities. -/
theorem sharpGeneration_selection {n N : ℕ} {s : ℕ} (hs : 1 ≤ s)
    (a : Fin (n + 2) → Fin N) (i : Fin (n + 2)) :
    selectionScale N i (a i).val ≤ sharpGeneration s a i.succ / (s : ℤ) ∧
      sharpGeneration s a i.succ / (s : ℤ) ≤
        selectionScale N i ((a i).val + 1) - 1 := by
  rw [generation_quotient hs]
  exact generationUnits_selection a i

/-- For coordinates `i≥3`, both selection-scale bounds are equalities. -/
theorem sharpGeneration_selection_eq {n N : ℕ} {s : ℕ} (hs : 1 ≤ s)
    (a : Fin (n + 2) → Fin N) (i : Fin (n + 2)) (hi : i ≠ 0) :
    selectionScale N i (a i).val = sharpGeneration s a i.succ / (s : ℤ) ∧
      sharpGeneration s a i.succ / (s : ℤ) =
        selectionScale N i ((a i).val + 1) - 1 := by
  rw [generation_quotient hs]
  revert hi
  refine Fin.cases ?_ (fun j => ?_) i
  · exact fun h => (h rfl).elim
  · intro _
    refine Fin.lastCases ?_ (fun l => ?_) j
    · simp [selectionScale, generationUnits]
      omega
    · simp [selectionScale, generationUnits]

end ReyZygmund.Sharpness
