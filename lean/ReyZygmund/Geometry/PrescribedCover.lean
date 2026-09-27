import ReyZygmund.Geometry.Rounding
import ReyZygmund.Geometry.ScalarCover
import ReyZygmund.Geometry.ShiftedGrid

/-!
# Concrete dyadic covers at the prescribed scale

The `3 ^ d` grids are the already constructed alternating shifted grids.
The closed original cube is contained in the half-open covering cube;
no boundary null-set modification is used. Zero dimension is allowed here.
-/

noncomputable section

open BoxIntegral
open scoped Classical

namespace ReyZygmund.Geometry

/-- There are exactly the prescribed number of shifted-grid indices. -/
theorem shifted_grid_index_card (d : ℕ) : Fintype.card (Fin d → Fin 3) = 3 ^ d := by
  simp

/-- Every cube has a cover in one of the concrete grids, with the
paper's prescribed side length, even for either convention on its boundary. -/
theorem prescribed_dyadic_cover {d : ℕ} (Q : Box (Fin d))
    (s : ℝ) (hs : 0 < s) (hwidth : ∀ i, Q.upper i - Q.lower i = s) :
    ∃ a : Fin d → Fin 3, ∃ P : Box (Fin d),
      P ∈ (shiftedDyadicGrid d a).cubes (-roundedScale s) ∧
      Set.Icc Q.lower Q.upper ⊆ (P : Set (Fin d → ℝ)) ∧
      ∀ i, P.upper i - P.lower i = (2 : ℝ) ^ roundedScale s := by
  let L : ℝ := (2 : ℝ) ^ roundedScale s
  let sigma : ℝ := (-1 : ℝ) ^ (-roundedScale s)
  have hL : 0 < L := zpow_pos (by norm_num) _
  have hsmall : 3 * s < L := by
    have h := (roundedScale_bounds hs).1
    change 4 * s ≤ L at h
    linarith
  have hsign : sigma = 1 ∨ sigma = -1 := by
    dsimp only [sigma]
    rw [neg_one_zpow_eq_ite]
    split_ifs <;> simp
  have hex (i : Fin d) := exists_shifted_interval_cover L s (Q.lower i) sigma
    hL hs hsmall hsign
  choose a z hlo hup using hex
  let P := shiftedDyadicCube a (-roundedScale s) z
  have hP : P ∈ (shiftedDyadicGrid d a).cubes (-roundedScale s) := ⟨z, rfl⟩
  refine ⟨a, P, hP, ?_, ?_⟩
  · intro x hx
    change ∀ i, P.lower i < x i ∧ x i ≤ P.upper i
    intro i
    have hl : P.lower i < Q.lower i := by
      simpa only [P, shiftedDyadicCube, rootBox, neg_neg, L, sigma] using hlo i
    have hu : Q.upper i < P.upper i := by
      have hi : Q.upper i = Q.lower i + s := by linarith [hwidth i]
      rw [hi]
      change Q.lower i + s <
        (2 : ℝ) ^ (-(-roundedScale s)) *
          ((z i : ℝ) + (-1 : ℝ) ^ (-roundedScale s) * ((a i).val : ℝ) / 3) +
            (2 : ℝ) ^ (-(-roundedScale s))
      simpa only [neg_neg, L, sigma, mul_add, mul_one] using hup i
    exact ⟨hl.trans_le (hx.1 i), (hx.2 i).trans hu.le⟩
  · intro i
    simpa only [neg_neg] using (shiftedDyadicGrid d a).width (-roundedScale s) P hP i

end ReyZygmund.Geometry
