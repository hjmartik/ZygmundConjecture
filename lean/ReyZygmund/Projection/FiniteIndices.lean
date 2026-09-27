import ReyZygmund.Geometry.ProductSteps
import ReyZygmund.Geometry.FinitePartition

/-! # Indices of the finite common projection

Each removed rectangle is counted once. Fixing all but one coordinate leaves
exactly the coordinate cubes contained in an eligible projection, allowing
equality. Interior indices exclude the smallest scale. Incomparability is not
needed.

-/

noncomputable section

open BoxIntegral
open scoped BigOperators Classical

namespace ReyZygmund.Projection

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- Product indices whose coordinate factors are above the cutoff. -/
def productInterior (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) :
    Finset (∀ i, Box (Fin (d i))) :=
  Fintype.piFinset (fun i => interior (I i) (N i))

@[simp] theorem mem_productInterior
    {I : ∀ i, Box (Fin (d i))} {N : Fin m → ℕ} {L : ∀ i, Box (Fin (d i))} :
    L ∈ productInterior I N ↔ ∀ i, L i ∈ interior (I i) (N i) :=
  Fintype.mem_piFinset

/-- The difference indices removed by the common projection, counted once. -/
def removedIndices (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) : Finset (∀ i, Box (Fin (d i))) :=
  (productInterior I N).filter (fun L => ∃ J ∈ G, ∀ i, L i ≤ J i)

/-- Projections of original rectangles containing the other fixed factors. -/
def eligibleProjections (j : Fin m) (G : Finset (∀ i, Box (Fin (d i))))
    (K : ∀ i, Box (Fin (d i))) : Finset (Box (Fin (d j))) :=
  (G.filter (fun J => ∀ i, i ≠ j → K i ≤ J i)).image (fun J => J j)

/-- The one-coordinate indices remaining in the projected difference sum. -/
def selectedCoordinateIndices (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (j : Fin m) (G : Finset (∀ i, Box (Fin (d i)))) (K : ∀ i, Box (Fin (d i))) :
    Finset (Box (Fin (d j))) :=
  (interior (I j) (N j)).filter
    (fun Q => ∃ J ∈ G, Q ≤ J j ∧ ∀ i, i ≠ j → K i ≤ J i)

theorem eligibleProjections_subset_descendants
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (j : Fin m) (G : Finset (∀ i, Box (Fin (d i)))) (K : ∀ i, Box (Fin (d i)))
    (hG : ∀ J ∈ G, ∀ i, J i ∈ descendants (I i) (N i)) :
    eligibleProjections j G K ⊆ descendants (I j) (N j) := by
  intro Q hQ
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hQ
  exact hG J (Finset.mem_filter.mp hJ).1 j

theorem selectedCoordinateIndices_eq_filter
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (j : Fin m) (G : Finset (∀ i, Box (Fin (d i)))) (K : ∀ i, Box (Fin (d i))) :
    selectedCoordinateIndices I N j G K =
      (interior (I j) (N j)).filter
        (fun L => ∃ Q ∈ eligibleProjections j G K, L ≤ Q) := by
  ext L
  simp only [selectedCoordinateIndices, Finset.mem_filter]
  constructor
  · rintro ⟨hL, J, hJ, hLJ, hKJ⟩
    exact ⟨hL, J j, Finset.mem_image.mpr ⟨J, Finset.mem_filter.mpr ⟨hJ, hKJ⟩, rfl⟩,
      hLJ⟩
  · rintro ⟨hL, Q, hQ, hLQ⟩
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hQ
    exact ⟨hL, J, (Finset.mem_filter.mp hJ).1, hLQ, (Finset.mem_filter.mp hJ).2⟩

/-- Fixing the other coordinates gives a bijection, not a sum over containing
rectangles. The value of the unused placeholder `K j` is irrelevant. -/
theorem removedIndices_fiber
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (j : Fin m) (G : Finset (∀ i, Box (Fin (d i)))) (K : ∀ i, Box (Fin (d i)))
    (hK : ∀ i, i ≠ j → K i ∈ interior (I i) (N i)) :
    (removedIndices I N G).filter (fun L => ∀ i, i ≠ j → L i = K i) =
      (selectedCoordinateIndices I N j G K).image (fun Q => Function.update K j Q) := by
  ext L
  constructor
  · intro hL
    obtain ⟨hL, hfixed⟩ := Finset.mem_filter.mp hL
    obtain ⟨hLi, J, hJ, hLJ⟩ := Finset.mem_filter.mp hL
    apply Finset.mem_image.mpr
    refine ⟨L j, Finset.mem_filter.mpr ⟨(mem_productInterior.mp hLi) j, J, hJ,
      hLJ j, ?_⟩, ?_⟩
    · intro i hij
      simpa only [hfixed i hij] using hLJ i
    · funext i
      by_cases hij : i = j
      · subst i
        simp
      · simp [hij, hfixed i hij]
  · intro hL
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨hQi, J, hJ, hQJ, hKJ⟩ := Finset.mem_filter.mp hQ
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨mem_productInterior.mpr ?_, J, hJ, ?_⟩, ?_⟩
    · intro i
      by_cases hij : i = j
      · subst i
        simpa using hQi
      · simpa [hij] using hK i hij
    · intro i
      by_cases hij : i = j
      · subst i
        simpa using hQJ
      · simpa [hij] using hKJ i hij
    · intro i hij
      simp [hij]

/-- The exact finite reindexing after the other-coordinate differences have
removed every unmatched product index. -/
theorem sum_removedIndices_fiber {V : Type*} [AddCommMonoid V]
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (j : Fin m) (G : Finset (∀ i, Box (Fin (d i)))) (K : ∀ i, Box (Fin (d i)))
    (hK : ∀ i, i ≠ j → K i ∈ interior (I i) (N i))
    (A : Box (Fin (d j)) → V) :
    (∑ L ∈ removedIndices I N G, if ∀ i, i ≠ j → L i = K i then A (L j) else 0) =
      ∑ Q ∈ selectedCoordinateIndices I N j G K, A Q := by
  rw [← Finset.sum_filter, removedIndices_fiber I N j G K hK]
  rw [Finset.sum_image]
  · simp
  · intro Q _ R _ hQR
    simpa using congrFun hQR j

end ReyZygmund.Projection
