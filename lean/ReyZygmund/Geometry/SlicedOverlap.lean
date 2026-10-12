import ReyZygmund.Geometry.LastCoordinate
import ReyZygmund.Overlap.Countable
import ReyZygmund.MathlibOnly.SubmittedDefinitions

/-!
# Weak incomparability and overlap of slices

The slicing lemma has three conclusions: weak incomparability,
a unique original rectangle for every slice member, and the pointwise overlap
identity. The geometric conclusions use the dyadic slice defined
in `RoundedSlices`. The overlap identity below reindexes the extended nonnegative
sum itself, so it needs no finiteness or finite-shadow-measure assumption.
-/

open BoxIntegral
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Geometry

open Overlap
open MathlibOnly.Submitted (WeaklyIncomparable)

variable {n : ℕ} {d : Fin (n + 1) → ℕ}

/-- The sliced family has no strict containment in every coordinate factor. -/
theorem sliceFamily_weaklyIncomparable
    (hn : 0 < n) (D : ∀ i, DyadicGrid (d i))
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) (hphi : Monotone phi)
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ roundedGridRectangles D phi)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (t : Fin (d (Fin.last n)) → ℝ) :
    WeaklyIncomparable (sliceFamily G t) := by
  intro P hP Q hQ hstrict
  obtain ⟨i, hi⟩ := sliceFamily_weaker_containment hn D phi hphi G hG hinc t
    P hP Q hQ (fun i => (hstrict i).le)
  exact (ne_of_lt (hstrict i)) hi

/-- Uniqueness of the original rectangle within a rounded slice.
Dyadicity and incomparability suffice; no rounded-scale hypothesis is needed. -/
theorem sliceFamily_existsUnique
    (D : ∀ i, DyadicGrid (d i)) (G : Set (∀ i, Box (Fin (d i))))
    (hG : G ⊆ gridRectangles D)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (t : Fin (d (Fin.last n)) → ℝ)
    {P : ∀ i : Fin n, Box (Fin (d i.castSucc))} (hP : P ∈ sliceFamily G t) :
    ∃! R, R ∈ G ∧ t ∈ R (Fin.last n) ∧ initialProjection R = P := by
  obtain ⟨R, ⟨hR, htR⟩, hRP⟩ := hP
  refine ⟨R, ⟨hR, htR, hRP⟩, ?_⟩
  rintro S ⟨hS, htS, hSP⟩
  exact initialProjection_injOn D G hG hinc t
    ⟨hS, htS⟩ ⟨hR, htR⟩ (hSP.trans hRP.symm)

/-- The sliced-overlap identity for an arbitrary set family. This equality
includes infinite overlap values and uses neither a finite-shadow assumption
nor an almost-everywhere qualification. -/
theorem overlap_splitLast_symm
    (D : ∀ i, DyadicGrid (d i)) (G : Set (∀ i, Box (Fin (d i))))
    (hG : G ⊆ gridRectangles D)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (y : Fin (∑ i : Fin n, d i.castSucc) → ℝ) (t : Fin (d (Fin.last n)) → ℝ) :
    overlap G ((splitLastCoordinates d).symm (y, t)) = overlap (sliceFamily G t) y := by
  let U : Set (∀ i, Box (Fin (d i))) := {R | R ∈ G ∧ t ∈ R (Fin.last n)}
  have hrectangle (R : ∀ i, Box (Fin (d i))) :
      (splitLastCoordinates d).symm (y, t) ∈ flatProductBox R ↔
        y ∈ flatProductBox (initialProjection R) ∧ t ∈ R (Fin.last n) := by
    simpa only [MeasurableEquiv.apply_symm_apply, Set.mem_prod, Box.mem_coe] using
      splitLastCoordinates_mem_rectangle d R ((splitLastCoordinates d).symm (y, t))
  calc
    overlap G ((splitLastCoordinates d).symm (y, t)) =
        ∑' R : U, (flatProductBox (initialProjection R.1) :
          Set (Fin (∑ i : Fin n, d i.castSucc) → ℝ)).indicator
            (fun _ => (1 : ℝ≥0∞)) y := by
      rw [overlap, tsum_subtype G (fun R =>
        (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)).indicator
          (fun _ => (1 : ℝ≥0∞)) ((splitLastCoordinates d).symm (y, t))),
        tsum_subtype U (fun R =>
          (flatProductBox (initialProjection R) :
            Set (Fin (∑ i : Fin n, d i.castSucc) → ℝ)).indicator
              (fun _ => (1 : ℝ≥0∞)) y)]
      apply tsum_congr
      intro R
      by_cases hR : R ∈ G
      · by_cases ht : t ∈ R (Fin.last n)
        · have hU : R ∈ U := ⟨hR, ht⟩
          rw [Set.indicator_of_mem hR, Set.indicator_of_mem hU]
          by_cases hy : y ∈ (flatProductBox (initialProjection R) :
              Set (Fin (∑ i : Fin n, d i.castSucc) → ℝ))
          · rw [Set.indicator_of_mem ((hrectangle R).mpr ⟨hy, ht⟩),
              Set.indicator_of_mem hy]
          · rw [Set.indicator_of_notMem (fun hx => hy ((hrectangle R).mp hx).1),
              Set.indicator_of_notMem hy]
        · have hU : R ∉ U := fun h => ht h.2
          rw [Set.indicator_of_mem hR, Set.indicator_of_notMem hU,
            Set.indicator_of_notMem (fun hx => ht ((hrectangle R).mp hx).2)]
      · have hU : R ∉ U := fun h => hR h.1
        rw [Set.indicator_of_notMem hR, Set.indicator_of_notMem hU]
    _ = overlap (sliceFamily G t) y := by
      symm
      exact tsum_image
        (fun P => (flatProductBox P :
          Set (Fin (∑ i : Fin n, d i.castSucc) → ℝ)).indicator
            (fun _ => (1 : ℝ≥0∞)) y)
        (initialProjection_injOn D G hG hinc t)

end ReyZygmund.Geometry
