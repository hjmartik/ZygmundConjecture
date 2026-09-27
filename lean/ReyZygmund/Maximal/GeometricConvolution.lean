import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# The geometric convolution in the signed-square argument

The series are real, summable, and indexed over all integers. The
natural kernel index starts at one through `j + 1`, matching the strict range
`n < N` in the paper. No finite-support hypothesis is imposed.
-/

open scoped BigOperators Classical

namespace ReyZygmund

private theorem hasSum_geometric_kernel (p : ℝ) (hp : p < 2) :
    HasSum (fun j : ℕ => Real.rpow 2 ((p - 2) * ((j + 1 : ℕ) : ℝ)))
      (1 / (Real.rpow 2 (2 - p) - 1)) := by
  let q := Real.rpow 2 (p - 2)
  let r := Real.rpow 2 (2 - p)
  have hq0 : 0 ≤ q :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg
    (by norm_num : (1 : ℝ) < 2) (sub_neg.mpr hp)
  have hqr : q * r = 1 := by
    dsimp only [q, r]
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      show p - 2 + (2 - p) = 0 by ring, Real.rpow_zero]
  have hden : 1 - q ≠ 0 := (sub_pos.mpr hq1).ne'
  have hr1 : r - 1 ≠ 0 := by
    intro heq
    have hr : r = 1 := by linarith
    rw [hr, mul_one] at hqr
    exact hq1.ne hqr
  have hvalue : q * (1 - q)⁻¹ = 1 / (r - 1) := by
    rw [← div_eq_mul_inv]
    apply (div_eq_div_iff hden hr1).mpr
    nlinarith [hqr]
  have hterm (j : ℕ) : Real.rpow 2 ((p - 2) * ((j + 1 : ℕ) : ℝ)) = q * q ^ j := by
    dsimp only [q]
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2), pow_succ, mul_comm]
  change HasSum _ (1 / (r - 1))
  rw [← hvalue]
  exact ((hasSum_geometric_of_lt_one hq0 hq1).mul_left q).congr_fun hterm

private theorem geometric_coefficient_le_three (p : ℝ) (hp : p ≤ (3 : ℝ) / 2) :
    1 / (Real.rpow 2 (2 - p) - 1) ≤ 3 := by
  have hhalf0 : 0 ≤ Real.rpow 2 ((1 : ℝ) / 2) :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
  have hhalf_sq : (Real.rpow 2 ((1 : ℝ) / 2)) ^ 2 = 2 := by
    have h := Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) ((1 : ℝ) / 2) (2 : ℝ)
    norm_num [Real.rpow_eq_pow, Real.rpow_two] at h ⊢
    exact h.symm
  have hhalf : (4 : ℝ) / 3 ≤ Real.rpow 2 ((1 : ℝ) / 2) := by
    nlinarith
  have hr : (4 : ℝ) / 3 ≤ Real.rpow 2 (2 - p) :=
    hhalf.trans (Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (by linarith))
  have hden : 0 < Real.rpow 2 (2 - p) - 1 := by linarith
  apply (div_le_iff₀ hden).mpr
  linarith

private theorem hasSum_int_sub (b : ℤ → ℝ) (hb : Summable b) (r : ℤ) :
    HasSum (fun n : ℤ => b (n - r)) (∑' n : ℤ, b n) := by
  let e : ℤ ≃ ℤ :=
    { toFun := fun n => n - r
      invFun := fun n => n + r
      left_inv := by
        intro n
        change (n - r) + r = n
        omega
      right_inv := by
        intro n
        change (n + r) - r = n
        omega }
  exact e.hasSum_iff.mpr hb.hasSum

/-- The two-index kernel is summable, including its infinite integer
tails. This is the convergence evidence for changing the order of summation. -/
theorem summable_geometric_convolution
    (p : ℝ) (_hp : 1 ≤ p) (hp3 : p ≤ (3 : ℝ) / 2)
    (b : ℤ → ℝ) (hb0 : ∀ n, 0 ≤ b n) (hb : Summable b) :
    Summable (fun z : ℤ × ℕ =>
      Real.rpow 2 ((p - 2) * ((z.2 + 1 : ℕ) : ℝ)) *
        b (z.1 - ((z.2 + 1 : ℕ) : ℤ))) := by
  have hp2 : p < 2 := by linarith only [hp3]
  have hcol (j : ℕ) :
      HasSum (fun N : ℤ => Real.rpow 2 ((p - 2) * ((j + 1 : ℕ) : ℝ)) *
        b (N - ((j + 1 : ℕ) : ℤ)))
        (Real.rpow 2 ((p - 2) * ((j + 1 : ℕ) : ℝ)) * ∑' n : ℤ, b n) :=
    (hasSum_int_sub b hb ((j + 1 : ℕ) : ℤ)).mul_left _
  have hcols : Summable (fun j : ℕ => ∑' N : ℤ,
      Real.rpow 2 ((p - 2) * ((j + 1 : ℕ) : ℝ)) *
        b (N - ((j + 1 : ℕ) : ℤ))) := by
    exact ((hasSum_geometric_kernel p hp2).summable.mul_right (∑' n : ℤ, b n)).congr
      (fun j => (hcol j).tsum_eq.symm)
  have hnonneg : 0 ≤ (fun z : ℕ × ℤ =>
      Real.rpow 2 ((p - 2) * ((z.1 + 1 : ℕ) : ℝ)) *
        b (z.2 - ((z.1 + 1 : ℕ) : ℤ))) := by
    intro z
    exact mul_nonneg (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le (hb0 _)
  have hprod := (summable_prod_of_nonneg hnonneg).mpr
    ⟨fun j => (hcol j).summable, hcols⟩
  exact hprod.prod_symm

/-- The outer series has the exact geometric coefficient from the
source, bounded by three throughout the closed exponent interval. -/
theorem geometric_convolution_sum
    (p : ℝ) (hp : 1 ≤ p) (hp3 : p ≤ (3 : ℝ) / 2)
    (b : ℤ → ℝ) (hb0 : ∀ n, 0 ≤ b n) (hb : Summable b) :
    HasSum (fun N : ℤ => ∑' j : ℕ,
      Real.rpow 2 ((p - 2) * ((j + 1 : ℕ) : ℝ)) *
        b (N - ((j + 1 : ℕ) : ℤ)))
      ((1 / (Real.rpow 2 (2 - p) - 1)) * ∑' n : ℤ, b n) ∧
      (∑' N : ℤ, ∑' j : ℕ,
        Real.rpow 2 ((p - 2) * ((j + 1 : ℕ) : ℝ)) *
          b (N - ((j + 1 : ℕ) : ℤ))) ≤ 3 * (∑' n : ℤ, b n) := by
  have hp2 : p < 2 := by linarith only [hp, hp3]
  let F : ℤ → ℕ → ℝ := fun N j =>
    Real.rpow 2 ((p - 2) * ((j + 1 : ℕ) : ℝ)) * b (N - ((j + 1 : ℕ) : ℤ))
  have hprod : Summable (Function.uncurry F) :=
    summable_geometric_convolution p hp hp3 b hb0 hb
  have hcol (j : ℕ) : HasSum (fun N : ℤ => F N j)
      (Real.rpow 2 ((p - 2) * ((j + 1 : ℕ) : ℝ)) * ∑' n : ℤ, b n) :=
    (hasSum_int_sub b hb ((j + 1 : ℕ) : ℤ)).mul_left _
  have hvalue : (∑' N : ℤ, ∑' j : ℕ, F N j) =
      (1 / (Real.rpow 2 (2 - p) - 1)) * ∑' n : ℤ, b n := by
    calc
      _ = ∑' j : ℕ, ∑' N : ℤ, F N j := hprod.tsum_comm.symm
      _ = ∑' j : ℕ, Real.rpow 2 ((p - 2) * ((j + 1 : ℕ) : ℝ)) *
          (∑' n : ℤ, b n) := tsum_congr (fun j => (hcol j).tsum_eq)
      _ = _ := ((hasSum_geometric_kernel p hp2).mul_right (∑' n : ℤ, b n)).tsum_eq
  have hs : HasSum (fun N : ℤ => ∑' j : ℕ, F N j)
      ((1 / (Real.rpow 2 (2 - p) - 1)) * ∑' n : ℤ, b n) :=
    hprod.prod.hasSum_iff.mpr hvalue
  refine ⟨hs, ?_⟩
  change (∑' N : ℤ, ∑' j : ℕ, F N j) ≤ _
  rw [hs.tsum_eq]
  exact mul_le_mul_of_nonneg_right (geometric_coefficient_le_three p hp3) (tsum_nonneg hb0)

/-- The strict integer row is summable. The map `j ↦ N-(j+1)`
identifies it exactly with the natural-index convolution; equality at `n=N`
is excluded, as in the original double sum. -/
theorem geometric_convolution_strict_reindex
    (p : ℝ) (hp : 1 ≤ p) (hp3 : p ≤ (3 : ℝ) / 2)
    (b : ℤ → ℝ) (hb0 : ∀ n, 0 ≤ b n) (hb : Summable b) (N : ℤ) :
    Summable (fun n : ℤ => if n < N then
      Real.rpow 2 ((2 - p) * (n : ℝ)) * b n else 0) ∧
      Real.rpow 2 ((p - 2) * (N : ℝ)) *
        (∑' n : ℤ, if n < N then Real.rpow 2 ((2 - p) * (n : ℝ)) * b n else 0) =
      ∑' j : ℕ, Real.rpow 2 ((p - 2) * ((j + 1 : ℕ) : ℝ)) *
        b (N - ((j + 1 : ℕ) : ℤ)) := by
  let c := Real.rpow 2 ((p - 2) * (N : ℝ))
  let g : ℤ → ℝ := fun n => if n < N then Real.rpow 2 ((2 - p) * (n : ℝ)) * b n else 0
  let e : ℕ → ℤ := fun j => N - ((j + 1 : ℕ) : ℤ)
  have he : Function.Injective e := by
    intro a b hab
    dsimp only [e] at hab
    omega
  have hz (n : ℤ) (hn : n ∉ Set.range e) : c * g n = 0 := by
    have hnN : ¬n < N := by
      intro hlt
      apply hn
      refine ⟨(N - n - 1).toNat, ?_⟩
      dsimp only [e]
      rw [Nat.cast_add, Nat.cast_one, Int.toNat_of_nonneg (by omega)]
      omega
    simp only [g, ite_eq_right hnN, mul_zero]
  have hterm (j : ℕ) : c * g (e j) =
      Real.rpow 2 ((p - 2) * ((j + 1 : ℕ) : ℝ)) *
        b (N - ((j + 1 : ℕ) : ℤ)) := by
    have hj : e j < N := by dsimp only [e]; omega
    dsimp only [c, g]
    rw [ite_eq_left hj, ← mul_assoc]
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    congr 1
    dsimp only [e]
    simp only [Int.cast_sub, Int.cast_natCast]
    ring
  have hrow := (summable_geometric_convolution p hp hp3 b hb0 hb).prod_factor N
  have hs : HasSum (fun n : ℤ => c * g n)
      (∑' j : ℕ, Real.rpow 2 ((p - 2) * ((j + 1 : ℕ) : ℝ)) *
        b (N - ((j + 1 : ℕ) : ℤ))) :=
    (he.hasSum_iff hz).mp (hrow.hasSum.congr_fun hterm)
  have hc : c ≠ 0 := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne'
  have hg : Summable g := (summable_mul_left_iff hc).mp hs.summable
  refine ⟨hg, ?_⟩
  change c * (∑' n : ℤ, g n) = _
  rw [← hg.tsum_mul_left c]
  exact hs.tsum_eq

end ReyZygmund
