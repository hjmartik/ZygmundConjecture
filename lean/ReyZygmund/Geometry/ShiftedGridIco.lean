import ReyZygmund.Geometry.ShiftedGrid
import ReyZygmund.Geometry.IcoGrid

/-! # Alternating shifted grids with `[lower, upper)` boundaries

The integer floor supplies coverage with the left-closed convention. The
existing cube grid's partition and nesting transfer by the corner geometry.
-/

noncomputable section

open BoxIntegral
open ReyZygmund.MathlibOnly

namespace ReyZygmund.Geometry

/-- The alternating shifted cubes are a grid also with the paper's boundary convention. -/
theorem shiftedDyadicGrid_IcoGrid (d : ℕ) (a : Fin d → Fin 3) :
    IcoGrid (shiftedDyadicGrid d a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k Q hQ R hR hne
    exact cubeIco_disjoint_iff.mpr
      ((shiftedDyadicGrid d a).pairwise_disjoint k hQ hR hne)
  · intro k x
    let z : Fin d → ℤ := fun i =>
      ⌊x i / (2 : ℝ) ^ k - (-1 : ℝ) ^ (-k) * ((a i).val : ℝ) / 3⌋
    refine ⟨shiftedDyadicCube a (-k) z, ⟨z, rfl⟩, ?_⟩
    intro i
    change (2 : ℝ) ^ (-(-k)) *
        ((z i : ℝ) + (-1 : ℝ) ^ (-k) * ((a i).val : ℝ) / 3) ≤ x i ∧
      x i < (2 : ℝ) ^ (-(-k)) *
        ((z i : ℝ) + (-1 : ℝ) ^ (-k) * ((a i).val : ℝ) / 3) +
          (2 : ℝ) ^ (-(-k))
    simp only [neg_neg]
    have hL : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
    constructor
    · exact (le_div_iff₀' hL).mp (le_sub_iff_add_le.mp (Int.floor_le _))
    · have hu := (div_lt_iff₀' hL).mp
        (sub_lt_iff_lt_add.mp (Int.lt_floor_add_one
          (x i / (2 : ℝ) ^ k - (-1 : ℝ) ^ (-k) * ((a i).val : ℝ) / 3)))
      calc
        x i < (2 : ℝ) ^ k *
            ((z i : ℝ) + 1 + (-1 : ℝ) ^ (-k) * ((a i).val : ℝ) / 3) := hu
        _ = (2 : ℝ) ^ k *
            ((z i : ℝ) + (-1 : ℝ) ^ (-k) * ((a i).val : ℝ) / 3) +
              (2 : ℝ) ^ k := by ring
  · intro k l Q R hQ hR
    rcases (shiftedDyadicGrid d a).nested k l Q R hQ hR with hdis | hQR | hRQ
    · exact Or.inl (cubeIco_disjoint_iff.mpr hdis)
    · exact Or.inr (Or.inl (cubeIco_subset_iff.mpr hQR))
    · exact Or.inr (Or.inr (cubeIco_subset_iff.mpr hRQ))

end ReyZygmund.Geometry
