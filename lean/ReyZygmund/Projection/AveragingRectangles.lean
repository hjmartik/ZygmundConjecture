import ReyZygmund.Projection.FiniteIndices

/-! # The finite family of averaging rectangles

These product descendants have a cross-coordinate partition cube in at least one
coordinate. The maximal partitions give coverage without incomparability;
incomparability is used to include every original rectangle.


-/

noncomputable section

open BoxIntegral
open scoped Classical

namespace ReyZygmund.Projection

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- Product descendants, including every coordinate cutoff level. -/
def productDescendants (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) :
    Finset (∀ i, Box (Fin (d i))) :=
  Fintype.piFinset (fun i => descendants (I i) (N i))

@[simp] theorem mem_productDescendants
    {I : ∀ i, Box (Fin (d i))} {N : Fin m → ℕ} {R : ∀ i, Box (Fin (d i))} :
    R ∈ productDescendants I N ↔ ∀ i, R i ∈ descendants (I i) (N i) :=
  Fintype.mem_piFinset

/-- The averaging family counts each rectangle and each projection once. It need not
be incomparable. -/
def averagingRectangles (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) : Finset (∀ i, Box (Fin (d i))) :=
  (productDescendants I N).filter (fun R =>
    ∃ j : Fin m, R j ∈ partitionCubes (I j) (N j) (eligibleProjections j G R))

@[simp] theorem mem_averagingRectangles
    {I : ∀ i, Box (Fin (d i))} {N : Fin m → ℕ}
    {G : Finset (∀ i, Box (Fin (d i)))} {R : ∀ i, Box (Fin (d i))} :
    R ∈ averagingRectangles I N G ↔
      (∀ i, R i ∈ descendants (I i) (N i)) ∧
        ∃ j : Fin m, R j ∈ partitionCubes (I j) (N j) (eligibleProjections j G R) := by
  simp only [averagingRectangles, Finset.mem_filter, mem_productDescendants]

theorem averagingRectangles_subset_productDescendants
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) :
    averagingRectangles I N G ⊆ productDescendants I N := by
  intro R hR
  exact (Finset.mem_filter.mp hR).1

theorem root_mem_productDescendants (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) :
    I ∈ productDescendants I N := by
  apply mem_productDescendants.mpr
  intro i
  exact mem_descendants.mpr ⟨0, Nat.zero_le _, by simp⟩

theorem productBox_subset_root_of_mem_productDescendants
    {I : ∀ i, Box (Fin (d i))} {N : Fin m → ℕ} {R : ∀ i, Box (Fin (d i))}
    (hR : R ∈ productDescendants I N) : productBox R ⊆ productBox I := by
  intro x hx
  apply (mem_productBox I x).mpr
  intro i
  exact le_of_mem_descendants (mem_productDescendants.mp hR i)
    ((mem_productBox R x).mp hx i)

/-- The unused coordinate placeholder does not affect eligible projections. -/
theorem eligibleProjections_update (j : Fin m)
    (G : Finset (∀ i, Box (Fin (d i)))) (K : ∀ i, Box (Fin (d i)))
    (P : Box (Fin (d j))) :
    eligibleProjections j G (Function.update K j P) = eligibleProjections j G K := by
  unfold eligibleProjections
  congr 1
  apply Finset.filter_congr
  intro R _
  constructor <;> intro h i hij <;> simpa [hij] using h i hij

/-- Refinement rules out a strictly larger smallest cube above a descendant.
The argument also works when a coordinate factor has dimension zero. -/
private theorem leaf_le_of_descendant_le {ι : Type*} [Fintype ι]
    {B R Q : Box ι} {n : ℕ} (hR : R ∈ descendants B n) (hQ : Q ∈ leaves B n)
    (hRQ : R ≤ Q) : Q ≤ R := by
  obtain ⟨k, hk, hRk⟩ := mem_descendants.mp hR
  obtain ⟨P, hP, hQP⟩ := level_refines B hk hQ
  have hRP : R = P := (level B k).eq_of_le_of_le hRk hP le_rfl (hRQ.trans hQP)
  exact hQP.trans hRP.symm.le

/-- Under incomparability, each original coordinate cube is maximal in its
cross-coordinate family. -/
theorem original_mem_partitionCubes
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (R : ∀ i, Box (Fin (d i))) (hR : R ∈ G) (j : Fin m) :
    R j ∈ partitionCubes (I j) (N j) (eligibleProjections j G R) := by
  apply mem_maximalCubes.mpr
  refine ⟨Finset.mem_union_left _ ?_, ?_⟩
  · exact Finset.mem_image.mpr
      ⟨R, Finset.mem_filter.mpr ⟨hR, fun _ _ => le_rfl⟩, rfl⟩
  · intro Q hQ hRQ
    rcases Finset.mem_union.mp hQ with hQe | hQl
    · obtain ⟨S, hS, hSj⟩ := Finset.mem_image.mp hQe
      obtain ⟨hSG, hRS⟩ := Finset.mem_filter.mp hS
      have heq : R = S := hinc R hR S hSG (by
        intro i
        by_cases hij : i = j
        · subst i
          rw [hSj]
          exact hRQ
        · exact hRS i hij)
      rw [← heq] at hSj
      exact hSj.symm.le
    · exact leaf_le_of_descendant_le (mem_productDescendants.mp (hG hR) j) hQl hRQ

/-- A positive number of coordinates lets each original rectangle meet the
existential partition condition defining the averaging family. -/
theorem original_subset_averagingRectangles (hm : 0 < m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S) :
    G ⊆ averagingRectangles I N G := by
  intro R hR
  exact mem_averagingRectangles.mpr ⟨mem_productDescendants.mp (hG hR),
    ⟨0, hm⟩, original_mem_partitionCubes I N G hG hinc R hR ⟨0, hm⟩⟩

/-- Replace one top cube factor by one of its cross-coordinate partition cubes. -/
theorem root_update_mem_averagingRectangles
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (j : Fin m) (P : Box (Fin (d j)))
    (hP : P ∈ partitionCubes (I j) (N j) (eligibleProjections j G I)) :
    Function.update I j P ∈ averagingRectangles I N G := by
  have he := eligibleProjections_subset_descendants I N j G I
    (fun R hR i => mem_productDescendants.mp (hG hR) i)
  have hPd := partitionCubes_subset_descendants he hP
  apply mem_averagingRectangles.mpr
  refine ⟨?_, j, ?_⟩
  · intro i
    by_cases hij : i = j
    · subst i
      simpa using hPd
    · simpa [hij] using mem_productDescendants.mp (root_mem_productDescendants I N) i
  · simpa only [Function.update_self, eligibleProjections_update] using hP

/-- The averaging rectangles with at most one factor different from its top cube already
give coverage. Incomparability is not needed. -/
theorem averagingRectangles_cover_at
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (j : Fin m) (x : ProductPoint d) (hx : x ∈ productBox I) :
    ∃ R ∈ averagingRectangles I N G,
      x ∈ productBox R ∧ ∀ i, i ≠ j → R i = I i := by
  have he := eligibleProjections_subset_descendants I N j G I
    (fun R hR i => mem_productDescendants.mp (hG hR) i)
  obtain ⟨P, hP, hxP⟩ := maximalPartition_isPartition (I j) (N j)
    (eligibleProjections j G I) he (x j) ((mem_productBox I x).mp hx j)
  refine ⟨Function.update I j P, root_update_mem_averagingRectangles I N G hG j P hP,
    ?_, ?_⟩
  · apply (mem_productBox _ x).mpr
    intro i
    by_cases hij : i = j
    · subst i
      simpa using hxP
    · simpa [hij] using (mem_productBox I x).mp hx i
  · intro i hij
    simp [hij]

/-- The averaging rectangles cover the top rectangle for every finite original
family of descendants, including the empty family. -/
theorem averagingRectangles_cover (hm : 0 < m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (x : ProductPoint d) (hx : x ∈ productBox I) :
    ∃ R ∈ averagingRectangles I N G, x ∈ productBox R := by
  obtain ⟨R, hR, hxR, _⟩ := averagingRectangles_cover_at I N G hG ⟨0, hm⟩ x hx
  exact ⟨R, hR, hxR⟩

/-- The averaging rectangles cover the top rectangle pointwise.
-/
theorem averagingRectangles_iUnion (hm : 0 < m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N) :
    (⋃ R ∈ averagingRectangles I N G, productBox R) = productBox I := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨R, hR, hxR⟩
    exact productBox_subset_root_of_mem_productDescendants
      (averagingRectangles_subset_productDescendants I N G hR) hxR
  · intro hx
    obtain ⟨R, hR, hxR⟩ := averagingRectangles_cover hm I N G hG x hx
    exact ⟨R, hR, hxR⟩

end ReyZygmund.Projection
