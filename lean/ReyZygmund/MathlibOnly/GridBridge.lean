import ReyZygmund.MathlibOnly.Definitions
import ReyZygmund.Geometry.GridOrder
import Mathlib.Tactic.Linarith

/-! # The two descriptions of a dyadic cube grid

The independent definition uses side-length exponents, partitions at every integer
scale and nesting of intersecting cubes. The proof library uses generation indices
and dyadic children. We prove both translations, preserving the boxes and
changing the index by `n = -k`. A common ancestor is not assumed. The argument
also covers dimension zero.

-/

noncomputable section

open BoxIntegral
open scoped Classical

namespace ReyZygmund.MathlibOnly

namespace CubeGrid

variable {d : ℕ} (D : CubeGrid d)

private theorem half_scale (k : ℤ) :
    (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ k / 2 := by
  rw [zpow_sub₀ (by norm_num), zpow_one]

/-- A half-size grid cube meeting a larger cube is contained in it. In zero
dimensions the coordinate-bound assertion is vacuous, as it should be. -/
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

/-- Convert the independent grid to the implementation's generation convention. -/
def toDyadicGrid : Geometry.DyadicGrid d where
  cubes n := D.cubes (-n)
  width n Q hQ i := D.side_length (-n) Q hQ i
  disjoint n := D.pairwise_disjoint (-n)
  cover n x := D.covers (-n) x
  children n Q hQ R hR := by
    have h := D.child_mem hQ hR
    simpa only [neg_add_rev, add_comm, sub_eq_add_neg] using h

@[simp] theorem toDyadicGrid_cubes (n : ℤ) :
    D.toDyadicGrid.cubes n = D.cubes (-n) := rfl

@[simp] theorem mem_toDyadicGrid_all {Q : Box (Fin d)} :
    (∃ n : ℤ, Q ∈ D.toDyadicGrid.cubes n) ↔ ∃ k : ℤ, Q ∈ D.cubes k := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨-n, hn⟩
  · rintro ⟨k, hk⟩
    exact ⟨-k, by simpa using hk⟩

theorem eq_of_cubes_eq {D E : CubeGrid d} (h : D.cubes = E.cubes) : D = E := by
  cases D
  cases E
  cases h
  rfl

end CubeGrid

/-- The implementation's dyadic children imply the paper's nesting
condition; no extra hypothesis on the grid is needed for the reverse map. -/
def ofDyadicGrid {d : ℕ} (D : Geometry.DyadicGrid d) : CubeGrid d where
  cubes k := D.cubes (-k)
  side_length k Q hQ i := by simpa using D.width (-k) Q hQ i
  pairwise_disjoint k := D.disjoint (-k)
  covers k x := D.cover (-k) x
  nested k l Q R hQ hR := by
    by_cases hdis : Disjoint (Q : Set (Fin d → ℝ)) (R : Set (Fin d → ℝ))
    · exact Or.inl hdis
    · obtain ⟨x, hxQ, hxR⟩ := Set.not_disjoint_iff.mp hdis
      exact Or.inr (D.nested_of_common_point hQ hR hxQ hxR)

@[simp] theorem ofDyadicGrid_cubes {d : ℕ} (D : Geometry.DyadicGrid d) (k : ℤ) :
    (ofDyadicGrid D).cubes k = D.cubes (-k) := rfl

@[simp] theorem of_toDyadicGrid {d : ℕ} (D : CubeGrid d) :
    ofDyadicGrid D.toDyadicGrid = D := by
  apply CubeGrid.eq_of_cubes_eq
  funext k
  simp

@[simp] theorem to_ofDyadicGrid_cubes {d : ℕ} (D : Geometry.DyadicGrid d) (n : ℤ) :
    (ofDyadicGrid D).toDyadicGrid.cubes n = D.cubes n := by
  simp

@[simp] theorem to_ofDyadicGrid {d : ℕ} (D : Geometry.DyadicGrid d) :
    (ofDyadicGrid D).toDyadicGrid = D := by
  have hext {D E : Geometry.DyadicGrid d} (h : D.cubes = E.cubes) : D = E := by
    cases D
    cases E
    cases h
    rfl
  apply hext
  funext n
  exact to_ofDyadicGrid_cubes D n

/-- The paper's nested partition grids and the implementation's dyadic
grids describe exactly the same boxes, at oppositely indexed scales. -/
def cubeGridEquivDyadicGrid (d : ℕ) : CubeGrid d ≃ Geometry.DyadicGrid d where
  toFun := CubeGrid.toDyadicGrid
  invFun := ofDyadicGrid
  left_inv := of_toDyadicGrid
  right_inv := to_ofDyadicGrid

end ReyZygmund.MathlibOnly
