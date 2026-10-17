import ReyZygmund.MathlibOnly.Definitions
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Tactic.Linarith

/-! # Cube containment with `[lower, upper)` boundaries

Changing both half-open boundary conventions preserves containment and
disjointness of boxes. These facts apply to the public `cubeIco` sets and
transfer the grid's nesting to their common-point geometry.
-/

open BoxIntegral
open ReyZygmund.MathlibOnly

namespace ReyZygmund.Geometry

variable {d : ℕ}

theorem cubeIco_eq_pi (Q : Box (Fin d)) :
    cubeIco Q = Set.pi Set.univ (fun i => Set.Ico (Q.lower i) (Q.upper i)) := by
  ext x
  simp only [cubeIco, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const,
    Set.mem_Ico]

/-- The two half-open conventions have the same containment relation. -/
theorem cubeIco_subset_iff {Q R : Box (Fin d)} :
    cubeIco Q ⊆ cubeIco R ↔ Q ≤ R := by
  have hne : (Set.pi Set.univ (fun i => Set.Ico (Q.lower i) (Q.upper i))).Nonempty :=
    ⟨Q.lower, fun i _ => ⟨le_rfl, Q.lower_lt_upper i⟩⟩
  rw [cubeIco_eq_pi, cubeIco_eq_pi, Set.pi_subset_pi_iff]
  simp only [hne.ne_empty, or_false, Set.mem_univ, forall_const]
  simp_rw [Set.Ico_subset_Ico_iff (Q.lower_lt_upper _)]
  rw [Box.le_iff_bounds]
  exact forall_and

/-- The two half-open conventions have the same disjointness relation. -/
theorem cubeIco_disjoint_iff {Q R : Box (Fin d)} :
    Disjoint (cubeIco Q) (cubeIco R) ↔
      Disjoint (Q : Set (Fin d → ℝ)) (R : Set (Fin d → ℝ)) := by
  rw [cubeIco_eq_pi, cubeIco_eq_pi, Q.coe_eq_pi, R.coe_eq_pi,
    Set.disjoint_pi, Set.disjoint_pi]
  simp only [Set.Ico_disjoint_Ico, Set.Ioc_disjoint_Ioc]

end ReyZygmund.Geometry

namespace ReyZygmund.MathlibOnly.CubeGrid

open ReyZygmund.Geometry

variable {d : ℕ} (D : CubeGrid d)

/-- Grid cubes with a common `[lower, upper)` point are nested. -/
theorem ico_nested_of_common_point {k l : ℤ} {Q R : Box (Fin d)}
    (hQ : Q ∈ D.cubes k) (hR : R ∈ D.cubes l)
    {x : Fin d → ℝ} (hxQ : x ∈ cubeIco Q) (hxR : x ∈ cubeIco R) :
    cubeIco Q ⊆ cubeIco R ∨ cubeIco R ⊆ cubeIco Q := by
  rcases D.nested k l Q R hQ hR with hdis | hQR | hRQ
  · exact False.elim (Set.disjoint_left.mp (cubeIco_disjoint_iff.mpr hdis) hxQ hxR)
  · exact Or.inl (cubeIco_subset_iff.mpr hQR)
  · exact Or.inr (cubeIco_subset_iff.mpr hRQ)

/-- Among intersecting grid cubes, increasing side exponents give containment. -/
theorem ico_subset_of_scale_le {k l : ℤ} {Q R : Box (Fin d)}
    (hQ : Q ∈ D.cubes k) (hR : R ∈ D.cubes l) (hkl : k ≤ l)
    {x : Fin d → ℝ} (hxQ : x ∈ cubeIco Q) (hxR : x ∈ cubeIco R) :
    cubeIco Q ⊆ cubeIco R := by
  rcases D.ico_nested_of_common_point hQ hR hxQ hxR with hQR | hRQ
  · exact hQR
  have hb := Box.le_iff_bounds.mp (cubeIco_subset_iff.mp hRQ)
  have hsize : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ l :=
    (zpow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).monotone hkl
  apply cubeIco_subset_iff.mpr
  apply Box.le_iff_bounds.mpr
  constructor <;> intro i <;>
    linarith [hb.1 i, hb.2 i, D.side_length k Q hQ i, D.side_length l R hR i]

end ReyZygmund.MathlibOnly.CubeGrid
