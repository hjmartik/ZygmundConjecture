import ReyZygmund.Geometry.FiniteCubes
import Mathlib.Order.Preorder.Finite

/-!
# Maximal members of the concrete finite descendant family

Eligible projections are a finite set, not a multiset. All smallest cubes are
inserted before maximal members are selected. No incomparability assumption is
placed on the eligible family.
-/

noncomputable section

open BoxIntegral
open scoped Classical

namespace ReyZygmund.Geometry

variable {ι : Type*}

/-- Inclusion-maximal boxes in a finite set. -/
def maximalCubes (s : Finset (Box ι)) : Finset (Box ι) := by
  classical
  exact s.filter fun P => ∀ Q ∈ s, P ≤ Q → Q ≤ P

@[simp] theorem mem_maximalCubes {s : Finset (Box ι)} {P : Box ι} :
    P ∈ maximalCubes s ↔ P ∈ s ∧ ∀ Q ∈ s, P ≤ Q → Q ≤ P := by
  classical
  simp [maximalCubes]

theorem maximalCubes_subset (s : Finset (Box ι)) : maximalCubes s ⊆ s := by
  intro P hP
  exact (mem_maximalCubes.mp hP).1

/-- Every member of a finite family is contained in one of its maximal members. -/
theorem exists_maximal_supercube {s : Finset (Box ι)} {P : Box ι} (hP : P ∈ s) :
    ∃ Q ∈ maximalCubes s, P ≤ Q := by
  obtain ⟨Q, hPQ, hQ⟩ := s.exists_le_maximal hP
  exact ⟨Q, mem_maximalCubes.mpr
    ⟨hQ.1, fun _ hR hQR => hQ.2 hR hQR⟩, hPQ⟩

variable [Fintype ι]

/-- The cubes defining the finite cross-coordinate partition. -/
def partitionCubes (I : Box ι) (N : ℕ) (eligible : Finset (Box ι)) : Finset (Box ι) := by
  classical
  exact maximalCubes (eligible ∪ leaves I N)

theorem partitionCubes_subset_descendants {I : Box ι} {N : ℕ}
    {eligible : Finset (Box ι)} (he : eligible ⊆ descendants I N) :
    partitionCubes I N eligible ⊆ descendants I N := by
  intro P hP
  rcases Finset.mem_union.mp (maximalCubes_subset _ hP) with h | h
  · exact he h
  · exact leaves_subset_descendants I N h

/-- Maximal descendants are disjoint, even when the eligible cubes overlap. -/
theorem partitionCubes_disjoint {I P Q : Box ι} {N : ℕ}
    {eligible : Finset (Box ι)} (he : eligible ⊆ descendants I N)
    (hP : P ∈ partitionCubes I N eligible) (hQ : Q ∈ partitionCubes I N eligible)
    (hne : P ≠ Q) : Disjoint (P : Set (ι → ℝ)) Q := by
  have hPd := partitionCubes_subset_descendants he hP
  have hQd := partitionCubes_subset_descendants he hQ
  have hPm := mem_maximalCubes.mp hP
  have hQm := mem_maximalCubes.mp hQ
  rcases descendants_nested_or_disjoint hPd hQd with hPQ | hQP | hd
  · exact (hne (le_antisymm hPQ (hPm.2 Q hQm.1 hPQ))).elim
  · exact (hne (le_antisymm (hQm.2 P hPm.1 hQP) hQP)).elim
  · exact hd

/-- The finite prepartition whose members are the selected maximal cubes. -/
def maximalPartition (I : Box ι) (N : ℕ) (eligible : Finset (Box ι))
    (he : eligible ⊆ descendants I N) : Prepartition I where
  boxes := partitionCubes I N eligible
  le_of_mem' := fun _ hP => le_of_mem_descendants (partitionCubes_subset_descendants he hP)
  pairwiseDisjoint := fun _ hP _ hQ hne => partitionCubes_disjoint he hP hQ hne

/-- Adjoining every smallest cube gives pointwise coverage of the top cube. -/
theorem maximalPartition_isPartition (I : Box ι) (N : ℕ) (eligible : Finset (Box ι))
    (he : eligible ⊆ descendants I N) : (maximalPartition I N eligible he).IsPartition := by
  intro x hx
  obtain ⟨Q, hQ, hxQ⟩ := level_isPartition I N x hx
  obtain ⟨P, hP, hQP⟩ :=
    exists_maximal_supercube (Finset.mem_union_right eligible (show Q ∈ leaves I N from hQ))
  exact ⟨P, hP, hQP hxQ⟩

/-- The partition-index identity, counting each member of either index set once. -/
theorem partition_indices [Nonempty ι] (I : Box ι) (N : ℕ)
    (eligible : Finset (Box ι)) :
    (interior I N).filter (fun L => ∃ J ∈ eligible, L ≤ J) =
      (interior I N).filter (fun L => ∃ P ∈ partitionCubes I N eligible, L ≤ P) := by
  classical
  ext L
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hL, J, hJ, hLJ⟩
    obtain ⟨P, hP, hJP⟩ := exists_maximal_supercube (Finset.mem_union_left (leaves I N) hJ)
    exact ⟨hL, P, hP, hLJ.trans hJP⟩
  · rintro ⟨hL, P, hP, hLP⟩
    rcases Finset.mem_union.mp (maximalCubes_subset _ hP) with hPe | hPleaf
    · exact ⟨hL, P, hPe, hLP⟩
    · exact (interior_not_le_leaf hL hPleaf hLP).elim

/-- Each selected difference cube is assigned to exactly one maximal cube. -/
theorem unique_partition_container {I L : Box ι} {N : ℕ}
    {eligible : Finset (Box ι)} (he : eligible ⊆ descendants I N)
    (hselected : ∃ J ∈ eligible, L ≤ J) :
    ∃! P, P ∈ partitionCubes I N eligible ∧ L ≤ P := by
  obtain ⟨J, hJ, hLJ⟩ := hselected
  obtain ⟨P, hP, hJP⟩ := exists_maximal_supercube (Finset.mem_union_left (leaves I N) hJ)
  refine ⟨P, ⟨hP, hLJ.trans hJP⟩, ?_⟩
  intro Q hQ
  exact (maximalPartition I N eligible he).eq_of_le_of_le hQ.1 hP hQ.2 (hLJ.trans hJP)

/-- In the empty-eligible case all and only the inserted smallest cubes are maximal. -/
@[simp] theorem partitionCubes_empty (I : Box ι) (N : ℕ) :
    partitionCubes I N ∅ = leaves I N := by
  classical
  ext P
  simp only [partitionCubes, Finset.empty_union, mem_maximalCubes]
  constructor
  · exact And.left
  · intro hP
    refine ⟨hP, fun Q hQ hPQ => ?_⟩
    exact ((level I N).eq_of_le hP hQ hPQ).symm.le

/-- Eligible cubes already at the smallest scale do not change that partition. -/
theorem partitionCubes_eq_leaves_of_subset {I : Box ι} {N : ℕ}
    {eligible : Finset (Box ι)} (he : eligible ⊆ leaves I N) :
    partitionCubes I N eligible = leaves I N := by
  rw [partitionCubes, Finset.union_eq_right.mpr he]
  simpa only [partitionCubes, Finset.empty_union] using partitionCubes_empty I N

/-- Paper-facing positive-dimensional instance of `eq:partition-indices`.
The eligible family is deduplicated; no incomparability assumption is imposed. -/
theorem finite_partition_indices (d : ℕ) (hd : 0 < d) (I : Box (Fin d)) (N : ℕ)
    (eligible : Finset (Box (Fin d))) :
    (interior I N).filter (fun L => ∃ J ∈ eligible, L ≤ J) =
      (interior I N).filter (fun L => ∃ P ∈ partitionCubes I N eligible, L ≤ P) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact partition_indices I N eligible

/-- The maximal cubes partition the top cube, and each selected interior cube is
contained in exactly one of them. The dimension is positive, as in the paper. -/
theorem finite_maximal_partition (d : ℕ) (_hd : 0 < d) (I : Box (Fin d)) (N : ℕ)
    (eligible : Finset (Box (Fin d))) (he : eligible ⊆ descendants I N) :
    (maximalPartition I N eligible he).IsPartition ∧
      ∀ L ∈ interior I N, (∃ J ∈ eligible, L ≤ J) →
        ∃! P, P ∈ partitionCubes I N eligible ∧ L ≤ P := by
  refine ⟨maximalPartition_isPartition I N eligible he, ?_⟩
  intro L _ hselected
  exact unique_partition_container he hselected

end ReyZygmund.Geometry
