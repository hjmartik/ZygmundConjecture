import ReyZygmund.Geometry.Rounding
import ReyZygmund.Geometry.ScalarCover
import ReyZygmund.Geometry.ShiftedGrid

/-!
# Dyadic covers at the prescribed scale

The `3 ^ d` alternating shifted grids cover every closed cube by a half-open
cube at the prescribed scale.
-/

noncomputable section

open BoxIntegral
open scoped Classical

open ReyZygmund.MathlibOnly (rounding cubeIco CubeGrid)

namespace ReyZygmund.Geometry

/-- There are exactly the prescribed number of shifted-grid indices. -/
theorem shifted_grid_index_card (d : ℕ) : Fintype.card (Fin d → Fin 3) = 3 ^ d := by
  simp

/-- The scalar placement gives strict room at both corners in every coordinate. -/
theorem prescribed_dyadic_cover_strict {d : ℕ} (Q : Box (Fin d))
    (s : ℝ) (hs : 0 < s) (hwidth : ∀ i, Q.upper i - Q.lower i = s) :
    ∃ a : Fin d → Fin 3, ∃ P : Box (Fin d),
      P ∈ (shiftedDyadicGrid d a).cubesAtGeneration (-rounding s) ∧
      ∀ i, P.lower i < Q.lower i ∧ Q.upper i < P.upper i := by
  let L : ℝ := (2 : ℝ) ^ rounding s
  let sigma : ℝ := (-1 : ℝ) ^ (-rounding s)
  have hL : 0 < L := zpow_pos (by norm_num) _
  have hsmall : 3 * s < L := by
    have h := (rounding_bounds hs).1
    change 4 * s ≤ L at h
    linarith
  have hsign : sigma = 1 ∨ sigma = -1 := by
    dsimp only [sigma]
    rw [neg_one_zpow_eq_ite]
    split_ifs <;> simp
  have hex (i : Fin d) := exists_shifted_interval_cover L s (Q.lower i) sigma
    hL hs hsmall hsign
  choose a z hlo hup using hex
  let P := shiftedDyadicCube a (-rounding s) z
  have hP : P ∈ (shiftedDyadicGrid d a).cubesAtGeneration (-rounding s) := by
    rw [shiftedDyadicGrid_cubesAtGeneration]
    exact ⟨z, rfl⟩
  refine ⟨a, P, hP, ?_⟩
  intro i
  constructor
  · simpa only [P, shiftedDyadicCube, rootBox, neg_neg, L, sigma] using hlo i
  · have hi : Q.upper i = Q.lower i + s := by linarith [hwidth i]
    rw [hi]
    change Q.lower i + s <
      (2 : ℝ) ^ (-(-rounding s)) *
        ((z i : ℝ) + (-1 : ℝ) ^ (-rounding s) * ((a i).val : ℝ) / 3) +
          (2 : ℝ) ^ (-(-rounding s))
    simpa only [neg_neg, L, sigma, mul_add, mul_one] using hup i

/-- Every closed cube has a cover in one of the shifted grids at the prescribed
side length. -/
theorem prescribed_dyadic_cover {d : ℕ} (Q : Box (Fin d))
    (s : ℝ) (hs : 0 < s) (hwidth : ∀ i, Q.upper i - Q.lower i = s) :
    ∃ a : Fin d → Fin 3, ∃ P : Box (Fin d),
      P ∈ (shiftedDyadicGrid d a).cubesAtGeneration (-rounding s) ∧
      Set.Icc Q.lower Q.upper ⊆ (P : Set (Fin d → ℝ)) ∧
      ∀ i, P.upper i - P.lower i = (2 : ℝ) ^ rounding s := by
  obtain ⟨a, P, hP, hcorners⟩ := prescribed_dyadic_cover_strict Q s hs hwidth
  refine ⟨a, P, hP, ?_, ?_⟩
  · intro x hx i
    exact ⟨(hcorners i).1.trans_le (hx.1 i), (hx.2 i).trans (hcorners i).2.le⟩
  · intro i
    simpa only [neg_neg] using (shiftedDyadicGrid d a).width (-rounding s) P hP i

/-- The same strict placement covers the closed cube with `[lower, upper)` boundaries. -/
theorem prescribed_dyadic_cover_Ico {d : ℕ} (Q : Box (Fin d))
    (s : ℝ) (hs : 0 < s) (hwidth : ∀ i, Q.upper i - Q.lower i = s) :
    ∃ a : Fin d → Fin 3, ∃ P : Box (Fin d),
      P ∈ (shiftedDyadicGrid d a).cubes (rounding s) ∧
      Set.Icc Q.lower Q.upper ⊆ cubeIco P := by
  obtain ⟨a, P, hP, hcorners⟩ := prescribed_dyadic_cover_strict Q s hs hwidth
  refine ⟨a, P, by simpa only [CubeGrid.cubesAtGeneration_neg] using hP, ?_⟩
  intro x hx i
  exact ⟨(hcorners i).1.le.trans (hx.1 i), (hx.2 i).trans_lt (hcorners i).2⟩

end ReyZygmund.Geometry
