import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! # The dyadic layer-cake comparison

The integer-indexed series uses real powers and strict level sets. Reindexing a
geometric series proves convergence before the series is compared with the power
of the function.

-/

open scoped BigOperators Classical

namespace ReyZygmund

private theorem hasSum_dyadic_Iic (p : ℝ) (hp : 0 < p) (k : ℤ) :
    HasSum (fun n : ℤ => if n ≤ k then Real.rpow 2 (p * (n : ℝ)) else 0)
      (Real.rpow 2 (p * (k : ℝ)) / (1 - Real.rpow 2 (-p))) := by
  let q := Real.rpow 2 (-p)
  have hq0 : 0 ≤ q := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-p)).le
  have hq1 : q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (neg_neg_of_pos hp)
  let e : ℕ → ℤ := fun r => k - r
  have he : Function.Injective e := by
    intro a b h
    dsimp only [e] at h
    omega
  have hz (n : ℤ) (hn : n ∉ Set.range e) :
      (if n ≤ k then Real.rpow 2 (p * (n : ℝ)) else 0) = 0 := by
    have hnk : ¬n ≤ k := by
      intro hle
      apply hn
      refine ⟨(k - n).toNat, ?_⟩
      dsimp only [e]
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hle)]
      omega
    rw [ite_eq_right hnk]
  have hterm (r : ℕ) :
      (if e r ≤ k then Real.rpow 2 (p * (e r : ℝ)) else 0) =
        Real.rpow 2 (p * (k : ℝ)) * q ^ r := by
    have hle : e r ≤ k := by dsimp only [e]; omega
    rw [ite_eq_left hle]
    dsimp only [e, q]
    simp only [Int.cast_sub, Int.cast_natCast, Real.rpow_eq_pow]
    rw [show p * ((k : ℝ) - (r : ℝ)) = p * (k : ℝ) + (-p) * (r : ℝ) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  have hnat : HasSum
      (fun r : ℕ => if e r ≤ k then Real.rpow 2 (p * (e r : ℝ)) else 0)
      (Real.rpow 2 (p * (k : ℝ)) / (1 - q)) := by
    simpa only [hterm, div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one hq0 hq1).mul_left (Real.rpow 2 (p * (k : ℝ)))
  exact (he.hasSum_iff hz).mp hnat

private theorem exists_dyadic_cutoff (t : ℝ) (ht : 0 < t) :
    ∃ k : ℤ, Real.rpow 2 (k : ℝ) < t ∧
      t ≤ Real.rpow 2 ((k + 1 : ℤ) : ℝ) ∧
        ∀ n : ℤ, Real.rpow 2 (n : ℝ) < t ↔ n ≤ k := by
  obtain ⟨k, hk⟩ := exists_mem_Ioc_zpow ht (by norm_num : (1 : ℝ) < 2)
  have hlo : Real.rpow 2 (k : ℝ) < t := by
    simpa only [Real.rpow_eq_pow, Real.rpow_intCast] using hk.1
  have hhi : t ≤ Real.rpow 2 ((k + 1 : ℤ) : ℝ) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_intCast] using hk.2
  refine ⟨k, hlo, hhi, ?_⟩
  intro n
  constructor
  · intro hn
    have hcast : (n : ℝ) < ((k + 1 : ℤ) : ℝ) :=
      (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp (hn.trans_le hhi)
    have hn' : n < k + 1 := by exact_mod_cast hcast
    omega
  · intro hn
    have hcast : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hn
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hcast).trans_lt hlo

private theorem hasSum_dyadic_zero (p : ℝ) :
    HasSum (fun n : ℤ => if Real.rpow 2 (n : ℝ) < 0 then
      Real.rpow 2 (p * (n : ℝ)) else 0) 0 := by
  have hzero : (fun n : ℤ => if Real.rpow 2 (n : ℝ) < 0 then
      Real.rpow 2 (p * (n : ℝ)) else 0) = fun _ : ℤ => (0 : ℝ) := by
    funext n
    simp only [Real.rpow_eq_pow]
    rw [ite_eq_right (not_lt.mpr
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (n : ℝ)).le)]
  rw [hzero]
  exact hasSum_zero

/-- The strict-threshold integer series converges for every
positive real exponent, including the zero input. -/
theorem summable_dyadic_layerCake (t p : ℝ) (ht : 0 ≤ t) (hp : 0 < p) :
    Summable (fun n : ℤ => if Real.rpow 2 (n : ℝ) < t then
      Real.rpow 2 (p * (n : ℝ)) else 0) := by
  rcases lt_or_eq_of_le ht with htpos | htzero
  · obtain ⟨k, _, _, hcut⟩ := exists_dyadic_cutoff t htpos
    simpa only [hcut] using (hasSum_dyadic_Iic p hp k).summable
  · subst t
    exact (hasSum_dyadic_zero p).summable

/-- The exact pointwise dyadic comparison in Section 2 of the paper.
The strict threshold and both endpoints of the exponent interval are retained. -/
theorem dyadic_layerCake_bounds (t p : ℝ) (ht : 0 ≤ t) (hp : 1 ≤ p)
    (hp3 : p ≤ (3 : ℝ) / 2) :
    Real.rpow t p / 4 ≤
        (∑' n : ℤ, if Real.rpow 2 (n : ℝ) < t then Real.rpow 2 (p * (n : ℝ)) else 0) ∧
      (∑' n : ℤ, if Real.rpow 2 (n : ℝ) < t then Real.rpow 2 (p * (n : ℝ)) else 0) ≤
        2 * Real.rpow t p := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  rcases lt_or_eq_of_le ht with htpos | htzero
  · obtain ⟨k, hlo, hhi, hcut⟩ := exists_dyadic_cutoff t htpos
    have hs : HasSum (fun n : ℤ => if Real.rpow 2 (n : ℝ) < t then
        Real.rpow 2 (p * (n : ℝ)) else 0)
        (Real.rpow 2 (p * (k : ℝ)) / (1 - Real.rpow 2 (-p))) := by
      simpa only [hcut] using hasSum_dyadic_Iic p hp0 k
    have hw0 : 0 ≤ Real.rpow 2 (p * (k : ℝ)) :=
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
    have hwS : Real.rpow 2 (p * (k : ℝ)) ≤
        ∑' n : ℤ, if Real.rpow 2 (n : ℝ) < t then Real.rpow 2 (p * (n : ℝ)) else 0 := by
      have h := hs.summable.le_tsum k (fun n _ => by
        by_cases hn : Real.rpow 2 (n : ℝ) < t
        · rw [ite_eq_left hn]
          exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
        · rw [ite_eq_right hn])
      simpa only [ite_eq_left hlo] using h
    have hpowp : Real.rpow 2 p ≤ 4 := by
      calc
        _ ≤ Real.rpow 2 2 :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
        _ = 4 := by norm_num [Real.rpow_eq_pow, Real.rpow_two]
    have htupper : Real.rpow t p ≤
        Real.rpow 2 (p * (k : ℝ)) * Real.rpow 2 p := by
      calc
        _ ≤ Real.rpow (Real.rpow 2 ((k + 1 : ℤ) : ℝ)) p :=
          Real.rpow_le_rpow htpos.le hhi hp0.le
        _ = _ := by
          simp only [Real.rpow_eq_pow]
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          simp only [Int.cast_add, Int.cast_one]
          rw [show ((k : ℝ) + 1) * p = p * (k : ℝ) + p by ring,
            Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have hwle : Real.rpow 2 (p * (k : ℝ)) ≤ Real.rpow t p := by
      calc
        _ = Real.rpow (Real.rpow 2 (k : ℝ)) p := by
          simp only [Real.rpow_eq_pow]
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring
        _ ≤ _ := Real.rpow_le_rpow
          (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (k : ℝ)).le hlo.le hp0.le
    have hqhalf : Real.rpow 2 (-p) ≤ (1 : ℝ) / 2 := by
      calc
        _ ≤ Real.rpow 2 (-1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
        _ = _ := by norm_num [Real.rpow_eq_pow, Real.rpow_neg_one]
    have hden : 0 < 1 - Real.rpow 2 (-p) := by linarith
    constructor
    · have hfour := htupper.trans (mul_le_mul_of_nonneg_left hpowp hw0)
      linarith
    · rw [hs.tsum_eq]
      calc
        _ ≤ 2 * Real.rpow 2 (p * (k : ℝ)) := by
          apply (div_le_iff₀ hden).mpr
          nlinarith [mul_le_mul_of_nonneg_left hqhalf hw0]
        _ ≤ _ := mul_le_mul_of_nonneg_left hwle (by norm_num : (0 : ℝ) ≤ 2)
  · subst t
    rw [(hasSum_dyadic_zero p).tsum_eq]
    simp only [Real.rpow_eq_pow, Real.zero_rpow hp0.ne', zero_div, mul_zero, le_refl, and_self]

end ReyZygmund
