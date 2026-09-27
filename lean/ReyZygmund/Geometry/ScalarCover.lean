import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Push

/-! # A pointwise cover by a shifted interval

Choose the endpoint immediately preceding the left endpoint in the one-third
lattice. Integer division selects one of the three shifted partitions. The
target's closed interval lies strictly inside the chosen interval, so either
half-open convention is covered.

-/

namespace ReyZygmund.Geometry

private theorem integer_thirds (j : ℤ) :
    ∃ a : Fin 3, ∃ z : ℤ, (j : ℝ) = 3 * (z : ℝ) + (a.val : ℝ) := by
  have h0 := Int.emod_nonneg j (by norm_num : (3 : ℤ) ≠ 0)
  have h3 := Int.emod_lt_of_pos j (by norm_num : (0 : ℤ) < 3)
  let a : Fin 3 := ⟨(j % 3).toNat, by omega⟩
  have ha : (a.val : ℤ) = j % 3 := by
    simp only [a, Int.toNat_of_nonneg h0]
  have hj : j = 3 * (j / 3) + (a.val : ℤ) := by omega
  refine ⟨a, j / 3, ?_⟩
  have h := congrArg (fun n : ℤ => (n : ℝ)) hj
  push_cast at h
  exact h

private theorem signed_integer_thirds (j : ℤ) (sigma : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) :
    ∃ a : Fin 3, ∃ z : ℤ,
      (j : ℝ) = 3 * (z : ℝ) + sigma * (a.val : ℝ) := by
  rcases hsigma with rfl | rfl
  · simpa only [one_mul] using integer_thirds j
  · obtain ⟨a, z, h⟩ := integer_thirds (-j)
    refine ⟨a, -z, ?_⟩
    push_cast at h ⊢
    linarith

/-- A closed interval of length less than one third of `L` is strictly inside
an interval of length `L` in one of the three prescribed shifted partitions. -/
theorem exists_shifted_interval_cover
    (L s u sigma : ℝ) (hL : 0 < L) (_hs : 0 < s)
    (hsmall : 3 * s < L) (hsigma : sigma = 1 ∨ sigma = -1) :
    ∃ a : Fin 3, ∃ z : ℤ,
      L * ((z : ℝ) + sigma * (a.val : ℝ) / 3) < u ∧
      u + s < L * ((z : ℝ) + sigma * (a.val : ℝ) / 3 + 1) := by
  let j : ℤ := ⌈3 * u / L⌉ - 1
  have hceil := (Int.ceil_eq_iff (a := 3 * u / L)
    (z := ⌈3 * u / L⌉)).mp rfl
  have hj : (j : ℝ) = (⌈3 * u / L⌉ : ℝ) - 1 := by
    simp only [j, Int.cast_sub, Int.cast_one]
  have hleft : (j : ℝ) < 3 * u / L := by linarith [hceil.1]
  have hright : 3 * u / L ≤ (j : ℝ) + 1 := by linarith [hceil.2]
  have hleft' := (lt_div_iff₀ hL).mp hleft
  have hright' := (div_le_iff₀ hL).mp hright
  obtain ⟨a, z, haz⟩ := signed_integer_thirds j sigma hsigma
  rw [haz] at hleft' hright'
  refine ⟨a, z, ?_, ?_⟩ <;> nlinarith

end ReyZygmund.Geometry
