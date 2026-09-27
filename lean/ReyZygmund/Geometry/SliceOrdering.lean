import ReyZygmund.Geometry.RoundedSlices
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Finset.Dedup

/-! # A finite ordering of the rectangles through a slice

Choose a last-coordinate generation for each grid rectangle, then sort the
finite slice by increasing generation. The list is a permutation, so equal
generations retain every distinct rectangle. Its `Fin` enumeration is
injective and the last boxes decrease by containment.
-/

open BoxIntegral
open scoped Classical

namespace ReyZygmund.Geometry

variable {n : ℕ} {d : Fin (n + 1) → ℕ}

/-- Enumerate exactly the rectangles through the fixed last-block point,
without repetitions, in decreasing order of their last boxes. No
incomparability, rounding, or positive-dimension hypothesis is needed. -/
theorem exists_ordered_slice_enumeration
    (D : ∀ i, DyadicGrid (d i)) (G : Finset (∀ i, Box (Fin (d i))))
    (hG : (↑G : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D)
    (t : Fin (d (Fin.last n)) → ℝ) :
    ∃ N : ℕ, ∃ R : Fin N → (∀ i, Box (Fin (d i))),
      Function.Injective R ∧
      (∀ S : ∀ i, Box (Fin (d i)),
        S ∈ G ∧ t ∈ S (Fin.last n) ↔ ∃ i, R i = S) ∧
      (∀ i j : Fin N, i < j → R j (Fin.last n) ≤ R i (Fin.last n)) := by
  let generation : (∀ i, Box (Fin (d i))) → ℤ := fun R =>
    if hR : R ∈ G then Classical.choose (hG hR (Fin.last n)) else 0
  have hgeneration (R : ∀ i, Box (Fin (d i))) (hR : R ∈ G) :
      R (Fin.last n) ∈ (D (Fin.last n)).cubes (generation R) := by
    simpa only [generation, dite_eq_left hR] using
      (Classical.choose_spec (hG hR (Fin.last n)))
  let S := G.filter (fun R => t ∈ R (Fin.last n))
  let cmp : (∀ i, Box (Fin (d i))) → (∀ i, Box (Fin (d i))) → Bool :=
    fun R T => decide (generation R ≤ generation T)
  let L := S.toList.mergeSort cmp
  have htrans : ∀ R T U, cmp R T → cmp T U → cmp R U := by
    intro R T U hRT hTU
    simp only [cmp, decide_eq_true_eq] at hRT hTU ⊢
    exact le_trans hRT hTU
  have htotal : ∀ R T, cmp R T || cmp T R := by
    intro R T
    simpa only [cmp, Bool.or_eq_true, decide_eq_true_eq] using
      le_total (generation R) (generation T)
  have hsorted : L.Pairwise (fun R T => generation R ≤ generation T) := by
    simpa only [L, cmp, decide_eq_true_eq] using
      (List.pairwise_mergeSort (le := cmp) htrans htotal S.toList)
  have hnodup : L.Nodup := S.nodup_toList.mergeSort
  have hmem (R : ∀ i, Box (Fin (d i))) :
      R ∈ L ↔ R ∈ G ∧ t ∈ R (Fin.last n) := by
    simp only [L, List.mem_mergeSort, Finset.mem_toList, S, Finset.mem_filter]
  refine ⟨L.length, L.get, hnodup.injective_get, ?_, ?_⟩
  · intro R
    exact (hmem R).symm.trans List.mem_iff_get
  · intro i j hij
    have hi := (hmem (L.get i)).mp (List.get_mem L i)
    have hj := (hmem (L.get j)).mp (List.get_mem L j)
    exact (D (Fin.last n)).le_of_generation_le
      (hgeneration (L.get i) hi.1) (hgeneration (L.get j) hj.1)
      (hsorted.rel_get_of_lt hij) hi.2 hj.2

/-- The first-coordinate projections of any exact slice enumeration have
precisely the existing slice family as their range. This does not
assert that the projection is injective. -/
theorem sliceFamily_eq_range_of_enumeration
    (G : Finset (∀ i, Box (Fin (d i)))) (t : Fin (d (Fin.last n)) → ℝ)
    {N : ℕ} (R : Fin N → (∀ i, Box (Fin (d i))))
    (hrange : ∀ S : ∀ i, Box (Fin (d i)),
      S ∈ G ∧ t ∈ S (Fin.last n) ↔ ∃ i, R i = S) :
    sliceFamily (↑G : Set (∀ i, Box (Fin (d i)))) t =
      Set.range (fun i => initialProjection (R i)) := by
  ext P
  constructor
  · rintro ⟨S, ⟨hS, htS⟩, hSP⟩
    obtain ⟨i, rfl⟩ := (hrange S).mp ⟨hS, htS⟩
    exact ⟨i, hSP⟩
  · rintro ⟨i, rfl⟩
    exact ⟨R i, (hrange (R i)).mpr ⟨i, rfl⟩, rfl⟩

end ReyZygmund.Geometry
