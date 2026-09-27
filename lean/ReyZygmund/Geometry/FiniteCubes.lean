import Mathlib.Analysis.BoxIntegral.Partition.SubboxInduction
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Data.Fintype.Powerset

/-! # Finite dyadic descendants

The construction uses Mathlib's half-open boxes `(lower, upper]`. Bisecting each
side preserves this convention at every boundary point and gives the finite
partitions used for averaging.

-/

noncomputable section

open BoxIntegral
open scoped Classical

namespace ReyZygmund.Geometry

/-- An arbitrarily located half-open cube with integer dyadic side length. -/
def rootBox {d : ℕ} (lower : Fin d → ℝ) (a : ℤ) : Box (Fin d) where
  lower := lower
  upper := fun i => lower i + (2 : ℝ) ^ a
  lower_lt_upper := fun _ => lt_add_of_pos_right _ (zpow_pos (by norm_num) _)

variable {ι : Type*} [Fintype ι]

/-- The partition obtained by bisecting every side at each of `n` steps. -/
def level (I : Box ι) : ℕ → Prepartition I
  | 0 => ⊤
  | n + 1 => (level I n).biUnion Prepartition.splitCenter

/-- All descendants through depth `N`, with each box included once. -/
def descendants (I : Box ι) (N : ℕ) : Finset (Box ι) := by
  classical
  exact (Finset.range (N + 1)).biUnion fun n => (level I n).boxes

/-- Difference indices: the descendants strictly above the final level. -/
def interior (I : Box ι) (N : ℕ) : Finset (Box ι) := by
  classical
  exact (Finset.range N).biUnion fun n => (level I n).boxes

/-- The smallest cubes in the finite construction. -/
def leaves (I : Box ι) (N : ℕ) : Finset (Box ι) :=
  (level I N).boxes

@[simp] theorem level_zero (I : Box ι) : level I 0 = ⊤ := rfl

@[simp] theorem level_succ (I : Box ι) (n : ℕ) :
    level I (n + 1) = (level I n).biUnion Prepartition.splitCenter := rfl

/-- Every level is a pointwise partition, including the top level. -/
theorem level_isPartition (I : Box ι) (n : ℕ) : (level I n).IsPartition := by
  induction n with
  | zero => exact Prepartition.isPartitionTop I
  | succ n ih =>
    exact ih.biUnion fun J _ => Prepartition.isPartition_splitCenter J

/-- Exact side lengths after repeatedly bisecting each side. -/
theorem width_of_mem_level {I J : Box ι} {n : ℕ} (hJ : J ∈ level I n) (i : ι) :
    J.upper i - J.lower i = (I.upper i - I.lower i) / (2 : ℝ) ^ n := by
  induction n generalizing J with
  | zero =>
    have hJI : J = I := Prepartition.mem_top.mp hJ
    subst J
    simp
  | succ n ih =>
    obtain ⟨K, hK, hJK⟩ := (level I n).mem_biUnion.mp hJ
    rw [Prepartition.upper_sub_lower_of_mem_splitCenter hJK, ih hK]
    simp [pow_succ, div_div]

@[simp] theorem rootBox_width {d : ℕ} (lower : Fin d → ℝ) (a : ℤ) (i : Fin d) :
    (rootBox lower a).upper i - (rootBox lower a).lower i = (2 : ℝ) ^ a := by
  simp [rootBox]

theorem rootBox_level_width {d : ℕ} {lower : Fin d → ℝ} {a : ℤ}
    {J : Box (Fin d)} {n : ℕ} (hJ : J ∈ level (rootBox lower a) n) (i : Fin d) :
    J.upper i - J.lower i = (2 : ℝ) ^ (a - (n : ℤ)) := by
  rw [width_of_mem_level hJ, rootBox_width, zpow_sub₀ (by norm_num), zpow_natCast]

/-- A finer level refines every earlier level. -/
theorem level_refines (I : Box ι) {m n : ℕ} (hmn : m ≤ n) :
    level I n ≤ level I m := by
  exact (antitone_nat_of_succ_le fun k =>
    (level I k).biUnion_le Prepartition.splitCenter) hmn

/-- A cube from a finer level is contained in, or disjoint from, a fixed coarser cube. -/
theorem level_le_or_disjoint {I J K : Box ι} {m n : ℕ} (hmn : m ≤ n)
    (hJ : J ∈ level I n) (hK : K ∈ level I m) :
    J ≤ K ∨ Disjoint (J : Set (ι → ℝ)) K := by
  obtain ⟨L, hL, hJL⟩ := level_refines I hmn hJ
  by_cases hLK : L = K
  · exact Or.inl (hLK ▸ hJL)
  · exact Or.inr (((level I m).disjoint_coe_of_mem hL hK hLK).mono_left hJL)

theorem level_nested_or_disjoint {I J K : Box ι} {m n : ℕ}
    (hJ : J ∈ level I m) (hK : K ∈ level I n) :
    J ≤ K ∨ K ≤ J ∨ Disjoint (J : Set (ι → ℝ)) K := by
  rcases le_total m n with hmn | hnm
  · rcases level_le_or_disjoint hmn hK hJ with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h.symm)
  · rcases level_le_or_disjoint hnm hJ hK with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

@[simp] theorem mem_descendants {I J : Box ι} {N : ℕ} :
    J ∈ descendants I N ↔ ∃ n ≤ N, J ∈ level I n := by
  classical
  simp only [descendants, Finset.mem_biUnion, Finset.mem_range,
    Nat.lt_succ_iff, Prepartition.mem_boxes]

@[simp] theorem mem_interior {I J : Box ι} {N : ℕ} :
    J ∈ interior I N ↔ ∃ n < N, J ∈ level I n := by
  classical
  simp only [interior, Finset.mem_biUnion, Finset.mem_range, Prepartition.mem_boxes]

@[simp] theorem mem_leaves {I J : Box ι} {N : ℕ} :
    J ∈ leaves I N ↔ J ∈ level I N := Iff.rfl

theorem le_of_mem_descendants {I J : Box ι} {N : ℕ} (hJ : J ∈ descendants I N) :
    J ≤ I := by
  obtain ⟨n, _, hn⟩ := mem_descendants.mp hJ
  exact (level I n).le_of_mem hn

theorem interior_subset_descendants (I : Box ι) (N : ℕ) :
    interior I N ⊆ descendants I N := by
  intro J hJ
  obtain ⟨n, hn, hJn⟩ := mem_interior.mp hJ
  exact mem_descendants.mpr ⟨n, hn.le, hJn⟩

theorem leaves_subset_descendants (I : Box ι) (N : ℕ) :
    leaves I N ⊆ descendants I N := by
  intro J hJ
  exact mem_descendants.mpr ⟨N, le_rfl, hJ⟩

theorem descendants_nested_or_disjoint {I J K : Box ι} {N : ℕ}
    (hJ : J ∈ descendants I N) (hK : K ∈ descendants I N) :
    J ≤ K ∨ K ≤ J ∨ Disjoint (J : Set (ι → ℝ)) K := by
  obtain ⟨m, _, hm⟩ := mem_descendants.mp hJ
  obtain ⟨n, _, hn⟩ := mem_descendants.mp hK
  exact level_nested_or_disjoint hm hn

/-- A difference index cannot be contained in an inserted smallest cube. -/
theorem interior_not_le_leaf [Nonempty ι] {I J Q : Box ι} {N : ℕ}
    (hJ : J ∈ interior I N) (hQ : Q ∈ leaves I N) : ¬ J ≤ Q := by
  obtain ⟨n, hn, hJn⟩ := mem_interior.mp hJ
  intro hJQ
  let i : ι := Classical.arbitrary ι
  have hb := Box.le_iff_bounds.mp hJQ
  have hwidth : J.upper i - J.lower i ≤ Q.upper i - Q.lower i := by
    linarith [hb.1 i, hb.2 i]
  rw [width_of_mem_level hJn, width_of_mem_level hQ] at hwidth
  have hstrict : (I.upper i - I.lower i) / (2 : ℝ) ^ N <
      (I.upper i - I.lower i) / (2 : ℝ) ^ n :=
    div_lt_div_of_pos_left (sub_pos.mpr (I.lower_lt_upper i))
      (pow_pos (by norm_num) n) (pow_lt_pow_right₀ (by norm_num) hn)
  exact (not_lt_of_ge hwidth) hstrict

/-- Containment reverses depth, because there is at least one positive-width coordinate. -/
theorem level_depth_le_of_le [Nonempty ι] {I J K : Box ι} {m n : ℕ}
    (hJ : J ∈ level I m) (hK : K ∈ level I n) (hJK : J ≤ K) : n ≤ m := by
  by_contra hnm
  exact interior_not_le_leaf (mem_interior.mpr ⟨m, Nat.lt_of_not_ge hnm, hJ⟩) hK hJK

theorem level_index_unique [Nonempty ι] {I J : Box ι} {m n : ℕ}
    (hm : J ∈ level I m) (hn : J ∈ level I n) : m = n :=
  le_antisymm (level_depth_le_of_le hn hm le_rfl) (level_depth_le_of_le hm hn le_rfl)

/-- Different depth levels have no repeated boxes. -/
theorem level_boxes_disjoint [Nonempty ι] (I : Box ι) {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (level I m).boxes (level I n).boxes := by
  classical
  exact Finset.disjoint_left.mpr fun _ hm hn => hmn (level_index_unique hm hn)

/-- Regrouping interior cubes by their unique depth introduces no multiplicity. -/
theorem sum_interior [Nonempty ι] {M : Type*} [AddCommMonoid M]
    (I : Box ι) (N : ℕ) (f : Box ι → M) :
    ∑ Q ∈ interior I N, f Q = ∑ n ∈ Finset.range N, ∑ Q ∈ (level I n).boxes, f Q := by
  classical
  exact Finset.sum_biUnion fun _ _ _ _ hmn => level_boxes_disjoint I hmn

/-- Subdividing every cube of a fixed level gives the corresponding later level. -/
theorem level_biUnion (I : Box ι) (n m : ℕ) :
    (level I n).biUnion (fun P => level P m) = level I (n + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      (level I n).biUnion (fun P => level P (m + 1)) =
          ((level I n).biUnion (fun P => level P m)).biUnion Prepartition.splitCenter :=
        Prepartition.biUnion_assoc _ _ (fun _ Q => Prepartition.splitCenter Q)
      _ = level I (n + (m + 1)) := by rw [ih]; rfl

theorem mem_level_add {I Q : Box ι} {n m : ℕ} :
    Q ∈ level I (n + m) ↔ ∃ P ∈ level I n, Q ∈ level P m := by
  rw [← level_biUnion, Prepartition.mem_biUnion]

/-- The descendants of a fixed cube are exactly the finer descendants of the top cube that it contains. -/
theorem mem_level_local {I P Q : Box ι} {n m : ℕ} (hP : P ∈ level I n) :
    Q ∈ level P m ↔ Q ∈ level I (n + m) ∧ Q ≤ P := by
  constructor
  · intro hQ
    exact ⟨mem_level_add.mpr ⟨P, hP, hQ⟩, (level P m).le_of_mem hQ⟩
  · rintro ⟨hQ, hQP⟩
    obtain ⟨R, hR, hQR⟩ := mem_level_add.mp hQ
    have hRP : R = P :=
      (level I n).eq_of_le_of_le hR hP ((level R m).le_of_mem hQR) hQP
    subst R
    exact hQR

/-- The local final level agrees with the global cutoff indices below `P`. -/
theorem leaves_localization {I P : Box ι} {n N : ℕ}
    (hP : P ∈ level I n) (hn : n ≤ N) :
    leaves P (N - n) = (leaves I N).filter (fun Q => Q ≤ P) := by
  classical
  ext Q
  simp only [Finset.mem_filter, mem_leaves, mem_level_local hP, Nat.add_sub_of_le hn]

/-- The local interior agrees with the global difference indices below `P`. -/
theorem interior_localization [Nonempty ι] {I P : Box ι} {n N : ℕ}
    (hP : P ∈ level I n) (hn : n ≤ N) :
    interior P (N - n) = (interior I N).filter (fun Q => Q ≤ P) := by
  classical
  ext Q
  simp only [Finset.mem_filter]
  constructor
  · intro hQ
    obtain ⟨m, hm, hQm⟩ := mem_interior.mp hQ
    have hloc := (mem_level_local hP).mp hQm
    exact ⟨mem_interior.mpr ⟨n + m, by omega, hloc.1⟩, hloc.2⟩
  · rintro ⟨hQ, hQP⟩
    obtain ⟨m, hm, hQm⟩ := mem_interior.mp hQ
    have hnm : n ≤ m := level_depth_le_of_le hQm hP hQP
    refine mem_interior.mpr ⟨m - n, by omega, (mem_level_local hP).mpr ⟨?_, hQP⟩⟩
    simpa only [Nat.add_sub_of_le hnm] using hQm

@[simp] theorem leaves_zero (I : Box ι) : leaves I 0 = {I} := rfl

@[simp] theorem interior_zero (I : Box ι) : interior I 0 = ∅ := by
  classical
  simp [interior]

/-- The paper's strict cutoff is the interior-depth predicate. -/
theorem rootBox_mem_interior_iff {d : ℕ} (i : Fin d) {lower : Fin d → ℝ} {a : ℤ}
    {J : Box (Fin d)} {N : ℕ} :
    J ∈ interior (rootBox lower a) N ↔ J ∈ descendants (rootBox lower a) N ∧
      (2 : ℝ) ^ (a - (N : ℤ)) < J.upper i - J.lower i := by
  constructor
  · intro hJ
    obtain ⟨n, hn, hJn⟩ := mem_interior.mp hJ
    refine ⟨mem_descendants.mpr ⟨n, hn.le, hJn⟩, ?_⟩
    rw [rootBox_level_width hJn]
    exact zpow_lt_zpow_right₀ (by norm_num) (by omega)
  · rintro ⟨hJ, hw⟩
    obtain ⟨n, hn, hJn⟩ := mem_descendants.mp hJ
    rw [rootBox_level_width hJn, zpow_lt_zpow_iff_right₀ (by norm_num)] at hw
    exact mem_interior.mpr ⟨n, by omega, hJn⟩

/-- The paper's equality cutoff is exactly the final descendant level. -/
theorem rootBox_mem_leaves_iff {d : ℕ} (i : Fin d) {lower : Fin d → ℝ} {a : ℤ}
    {J : Box (Fin d)} {N : ℕ} :
    J ∈ leaves (rootBox lower a) N ↔ J ∈ descendants (rootBox lower a) N ∧
      J.upper i - J.lower i = (2 : ℝ) ^ (a - (N : ℤ)) := by
  constructor
  · intro hJ
    exact ⟨leaves_subset_descendants _ _ hJ, rootBox_level_width hJ i⟩
  · rintro ⟨hJ, hw⟩
    obtain ⟨n, _, hJn⟩ := mem_descendants.mp hJ
    rw [rootBox_level_width hJn] at hw
    have hexp := (zpow_right_strictMono₀ (show (1 : ℝ) < 2 by norm_num)).injective hw
    have hnN : n = N := by omega
    subst n
    exact hJn

/-- Bisecting each side of a `d`-dimensional box gives `2^d` children. -/
theorem splitCenter_card (I : Box ι) :
    (Prepartition.splitCenter I).boxes.card = 2 ^ Fintype.card ι := by
  simp [Prepartition.splitCenter, Fintype.card_set]

end ReyZygmund.Geometry
