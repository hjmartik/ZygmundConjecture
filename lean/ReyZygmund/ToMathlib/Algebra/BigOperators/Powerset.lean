import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! # Isolating the full set in an alternating subset sum -/

open scoped BigOperators

namespace Finset

/-- If an alternating sum over all subsets vanishes, its full-set term is the
corresponding signed sum over proper subsets. -/
theorem eq_sum_ssubsets_of_sum_powerset_eq_zero
    {α R : Type*} [DecidableEq α] [CommRing R]
    (s : Finset α) (a : Finset α → R)
    (h : ∑ t ∈ s.powerset, (-1 : R) ^ t.card * a t = 0) :
    a s = ∑ t ∈ s.ssubsets, (-1 : R) ^ (s.card + 1 + t.card) * a t := by
  let S := ∑ t ∈ s.ssubsets, (-1 : R) ^ t.card * a t
  have hsplit : (-1 : R) ^ s.card * a s + S = 0 := by
    have heq := (Finset.add_sum_erase s.powerset
      (fun t => (-1 : R) ^ t.card * a t) (by simp : s ∈ s.powerset)).trans h
    simpa only [S, Finset.ssubsets] using heq
  have hval : (-1 : R) ^ s.card * a s = -S :=
    eq_neg_of_add_eq_zero_left hsplit
  have hsign : (-1 : R) ^ s.card * (-1 : R) ^ s.card = 1 := by
    rw [← mul_pow]
    simp
  calc
    a s = ((-1 : R) ^ s.card * (-1 : R) ^ s.card) * a s := by
      rw [hsign, one_mul]
    _ = (-1 : R) ^ s.card * ((-1 : R) ^ s.card * a s) := by ring
    _ = -((-1 : R) ^ s.card) * S := by rw [hval]; ring
    _ = ∑ t ∈ s.ssubsets,
        -((-1 : R) ^ s.card) * ((-1 : R) ^ t.card * a t) := by
      exact Finset.mul_sum _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      simp only [pow_add, pow_one]
      ring

end Finset
