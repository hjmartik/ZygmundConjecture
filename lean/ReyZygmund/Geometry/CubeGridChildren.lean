import ReyZygmund.MathlibOnly.Definitions
import Mathlib.Analysis.BoxIntegral.Partition.SubboxInduction
import Mathlib.Tactic.Linarith

/-! # Children of a dyadic cube grid

A cube at side exponent `k` has its midpoint children at exponent `k - 1`.
The partition and nesting properties determine these children.
-/

noncomputable section

open BoxIntegral
open scoped Classical

namespace ReyZygmund.MathlibOnly.CubeGrid

variable {d : ℕ} (D : CubeGrid d)

/-- Generation `n` consists of cubes of side length `2 ^ (-n)`.
The grid itself retains its side-length exponent indexing. -/
abbrev cubesAtGeneration (n : ℤ) : Set (Box (Fin d)) := D.cubes (-n)

private theorem half_scale (k : ℤ) :
    (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ k / 2 := by
  rw [zpow_sub₀ (by norm_num), zpow_one]

/-- A half-size grid cube meeting a larger cube is contained in it. -/
theorem halfScale_le_of_common_point {k : ℤ} {Q R : Box (Fin d)}
    (hQ : Q ∈ D.cubes k) (hR : R ∈ D.cubes (k - 1))
    {x : Fin d → ℝ} (hxQ : x ∈ Q) (hxR : x ∈ R) : R ≤ Q := by
  rcases D.nested k (k - 1) Q R hQ hR with hdis | hQR | hRQ
  · exact False.elim (Set.disjoint_left.mp hdis hxQ hxR)
  · have hb := Box.le_iff_bounds.mp hQR
    have hbad (i : Fin d) : False := by
      have hwidthQ := D.side_length k Q hQ i
      have hwidthR := D.side_length (k - 1) R hR i
      rw [half_scale] at hwidthR
      have hpos : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
      linarith [hb.1 i, hb.2 i]
    exact Box.le_iff_bounds.mpr
      ⟨fun i => (hbad i).elim, fun i => (hbad i).elim⟩
  · exact hRQ

/-- The lower endpoint of a contained half-size grid cube is either the
parent's lower endpoint or its midpoint, in every coordinate. -/
theorem lower_eq_lower_or_midpoint {k : ℤ} {Q R : Box (Fin d)}
    (hQ : Q ∈ D.cubes k) (hR : R ∈ D.cubes (k - 1)) (hRQ : R ≤ Q)
    (i : Fin d) :
    R.lower i = Q.lower i ∨ R.lower i = (Q.lower i + Q.upper i) / 2 := by
  have hb := Box.le_iff_bounds.mp hRQ
  have hwidthQ := D.side_length k Q hQ i
  have hwidthR := D.side_length (k - 1) R hR i
  rw [half_scale] at hwidthR
  by_cases heq : R.lower i = Q.lower i
  · exact Or.inl heq
  right
  apply le_antisymm
  · linarith [hb.2 i]
  by_contra hmid
  have hltmid : R.lower i < (Q.lower i + Q.upper i) / 2 := lt_of_not_ge hmid
  have hltlower : Q.lower i < R.lower i :=
    lt_of_le_of_ne (hb.1 i) (fun h => heq h.symm)
  let x : Fin d → ℝ := Function.update R.upper i (R.lower i)
  have hxQ : x ∈ Q := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [x, Function.update_self, Set.mem_Ioc] using
        (show Q.lower i < R.lower i ∧ R.lower i ≤ Q.upper i by
          constructor
          · exact hltlower
          · linarith [R.lower_lt_upper i, hb.2 i])
    · simpa only [x, Function.update_of_ne hji] using hRQ R.upper_mem j
  obtain ⟨S, hS, hxS⟩ := D.covers (k - 1) x
  have hSQ : S ≤ Q := D.halfScale_le_of_common_point hQ hS hxQ hxS
  have hwidthS := D.side_length (k - 1) S hS i
  rw [half_scale] at hwidthS
  have hSupper : R.lower i < S.upper i := by
    linarith [(Box.le_iff_bounds.mp hSQ).1 i]
  have hxSi : S.lower i < R.lower i := by
    simpa only [x, Function.update_self] using (hxS i).1
  have hne : R ≠ S := by
    intro h
    have := h ▸ hxSi
    exact (lt_irrefl _ this)
  let y : Fin d → ℝ :=
    Function.update R.upper i (min (S.upper i) (R.upper i))
  have hyR : y ∈ R := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [y, Function.update_self, Set.mem_Ioc] using
        (show R.lower i < min (S.upper i) (R.upper i) ∧
            min (S.upper i) (R.upper i) ≤ R.upper i from
          ⟨lt_min hSupper (R.lower_lt_upper i), min_le_right _ _⟩)
    · simpa only [y, Function.update_of_ne hji] using R.upper_mem j
  have hyS : y ∈ S := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [y, Function.update_self, Set.mem_Ioc] using
        (show S.lower i < min (S.upper i) (R.upper i) ∧
            min (S.upper i) (R.upper i) ≤ S.upper i from
          ⟨lt_min (hxSi.trans hSupper) (hxSi.trans (R.lower_lt_upper i)),
            min_le_left _ _⟩)
    · simpa only [x, y, Function.update_of_ne hji] using hxS j
  exact Set.disjoint_left.mp (D.pairwise_disjoint (k - 1) hR hS hne) hyR hyS

/-- A grid cube contained in another at the next smaller scale is one of its
dyadic children, obtained by bisecting each side of the parent. -/
theorem mem_splitCenter_of_halfScale {k : ℤ} {Q R : Box (Fin d)}
    (hQ : Q ∈ D.cubes k) (hR : R ∈ D.cubes (k - 1)) (hRQ : R ≤ Q) :
    R ∈ Prepartition.splitCenter Q := by
  refine Prepartition.mem_splitCenter.mpr ⟨{i | R.lower i ≠ Q.lower i}, ?_⟩
  have hcorners (i : Fin d) :
      (Q.splitCenterBox {j | R.lower j ≠ Q.lower j}).lower i = R.lower i ∧
      (Q.splitCenterBox {j | R.lower j ≠ Q.lower j}).upper i = R.upper i := by
    have hwidthQ := D.side_length k Q hQ i
    have hwidthR := D.side_length (k - 1) R hR i
    rw [half_scale] at hwidthR
    have hchoice := D.lower_eq_lower_or_midpoint hQ hR hRQ i
    simp only [Box.splitCenterBox, Set.piecewise, Set.mem_ofPred_eq]
    split_ifs with h
    · have hmid := hchoice.resolve_left h
      constructor <;> linarith
    · have hlower : R.lower i = Q.lower i := not_not.mp h
      constructor <;> linarith
  apply Box.ext
  intro x
  simp only [Box.mem_def]
  apply forall_congr'
  intro i
  rw [(hcorners i).1, (hcorners i).2]

/-- Every dyadic child occurs at the next smaller scale. Cover its
upper corner and use uniqueness in the partition into children. -/
theorem child_mem {k : ℤ} {Q R : Box (Fin d)}
    (hQ : Q ∈ D.cubes k) (hR : R ∈ Prepartition.splitCenter Q) :
    R ∈ D.cubes (k - 1) := by
  obtain ⟨S, hS, hxS⟩ := D.covers (k - 1) R.upper
  have hxQ : R.upper ∈ Q := (Prepartition.splitCenter Q).le_of_mem hR R.upper_mem
  have hSQ := D.halfScale_le_of_common_point hQ hS hxQ hxS
  have hSchild := D.mem_splitCenter_of_halfScale hQ hS hSQ
  have hSR : S = R :=
    (Prepartition.splitCenter Q).eq_of_mem_of_mem hSchild hR hxS R.upper_mem
  exact hSR ▸ hS

end ReyZygmund.MathlibOnly.CubeGrid
