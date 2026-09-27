import ReyZygmund.Sharpness.RetainedPartition
import ReyZygmund.Geometry.ProductSteps
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! # Finite partitions in the sharpness construction

Refinement to a finer integer generation preserves the union. Products of
coordinate partitions give a product partition and a pointwise indicator identity.
These facts describe the sharpness family at a fixed scale tuple.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Sharpness

open Geometry

/-- Refine a finite same-generation family by its dyadic descendants.
The equality is pointwise, including all half-open boundary points. -/
theorem refine_grid_partition {d : ℕ} (D : DyadicGrid d) (n g : ℤ) (hng : n ≤ g)
    (P : Finset (Box (Fin d))) (hP : ∀ Q ∈ P, Q ∈ D.cubes n) :
    let F := P.biUnion (fun Q => (level Q (g - n).toNat).boxes)
    (∀ R ∈ F, R ∈ D.cubes g) ∧
      boxUnion F = boxUnion P ∧
      Set.PairwiseDisjoint (↑F : Set (Box (Fin d)))
        (fun R => (R : Set (Fin d → ℝ))) ∧
      ∀ R ∈ F, ∃ Q ∈ P, R ≤ Q := by
  let F := P.biUnion (fun Q => (level Q (g - n).toNat).boxes)
  have hdepth : n + ((g - n).toNat : ℤ) = g := by omega
  have hgen (R : Box (Fin d)) (hR : R ∈ F) : R ∈ D.cubes g := by
    obtain ⟨Q, hQ, hRQ⟩ := Finset.mem_biUnion.mp hR
    simpa only [hdepth] using D.mem_cubes_of_mem_level (hP Q hQ) hRQ
  refine ⟨hgen, boxUnion_level_biUnion P (g - n).toNat, ?_, ?_⟩
  · intro R hR S hS hne
    exact D.disjoint g (hgen R hR) (hgen S hS) hne
  · intro R hR
    obtain ⟨Q, hQ, hRQ⟩ := Finset.mem_biUnion.mp hR
    exact ⟨Q, hQ, (level Q (g - n).toNat).le_of_mem hRQ⟩

private theorem product_boxUnion_eq {m : ℕ} {d : Fin m → ℕ}
    (P : ∀ i, Finset (Box (Fin (d i)))) :
    (⋃ R ∈ Fintype.piFinset P, productBox R) =
      Set.pi Set.univ (fun i => boxUnion (P i)) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ_pi]
  constructor
  · rintro ⟨R, hR, hxR⟩ i
    simp only [boxUnion, Set.mem_iUnion]
    exact ⟨R i, Fintype.mem_piFinset.mp hR i, (mem_productBox R x).mp hxR i⟩
  · intro hx
    have hi (i : Fin m) : ∃ Q ∈ P i, x i ∈ (Q : Set (Fin (d i) → ℝ)) := by
      simpa only [boxUnion, Set.mem_iUnion, exists_prop] using hx i
    choose R hR hxR using hi
    exact ⟨R, Fintype.mem_piFinset.mpr hR, (mem_productBox R x).mpr hxR⟩

/-- Products of same-generation coordinate families partition the
product of their unions. The indicator identity is real-valued and pointwise. -/
theorem product_grid_partition {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ)
    (P : ∀ i, Finset (Box (Fin (d i))))
    (hP : ∀ i Q, Q ∈ P i → Q ∈ (D i).cubes (n i)) :
    (⋃ R ∈ Fintype.piFinset P, productBox R) =
        Set.pi Set.univ (fun i => boxUnion (P i)) ∧
      Set.PairwiseDisjoint
        (↑(Fintype.piFinset P) : Set (∀ i, Box (Fin (d i)))) productBox ∧
      ∀ x : ProductPoint d,
        (∑ R ∈ Fintype.piFinset P,
          (productBox R).indicator (fun _ => (1 : ℝ)) x) =
          ∏ i, (boxUnion (P i)).indicator (fun _ => (1 : ℝ)) (x i) := by
  have hcover := product_boxUnion_eq P
  have hdis : Set.PairwiseDisjoint
      (↑(Fintype.piFinset P) : Set (∀ i, Box (Fin (d i)))) productBox := by
    intro R hR S hS hne
    apply Set.disjoint_left.mpr
    intro x hxR hxS
    apply hne
    funext i
    exact (D i).eq_of_mem_of_mem
      (hP i (R i) (Fintype.mem_piFinset.mp hR i))
      (hP i (S i) (Fintype.mem_piFinset.mp hS i))
      ((mem_productBox R x).mp hxR i) ((mem_productBox S x).mp hxS i)
  refine ⟨hcover, hdis, ?_⟩
  intro x
  have hsum : (∑ R ∈ Fintype.piFinset P,
        (productBox R).indicator (fun _ => (1 : ℝ)) x) =
      (Set.pi Set.univ (fun i => boxUnion (P i))).indicator
        (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ Set.pi Set.univ (fun i => boxUnion (P i))
    · have hxcover : x ∈ ⋃ R ∈ Fintype.piFinset P, productBox R := by
        rw [hcover]
        exact hx
      obtain ⟨R, hxR⟩ := Set.mem_iUnion.mp hxcover
      obtain ⟨hR, hxR⟩ := Set.mem_iUnion.mp hxR
      rw [Finset.sum_eq_single R]
      · simp only [Set.indicator_of_mem hxR, Set.indicator_of_mem hx]
      · intro S hS hSR
        exact Set.indicator_of_notMem
          (fun hxS => Set.disjoint_left.mp (hdis hS hR hSR) hxS hxR) _
      · intro hnot
        exact (hnot hR).elim
    · rw [Set.indicator_of_notMem hx]
      apply Finset.sum_eq_zero
      intro R hR
      apply Set.indicator_of_notMem
      intro hxR
      apply hx
      rw [← hcover]
      exact Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨hR, hxR⟩⟩
  rw [hsum]
  simpa only [Finset.coe_univ, Pi.one_def] using
    (Set.indicator_pi_one_apply (M₀ := ℝ) (Finset.univ : Finset (Fin m))
      (fun i => boxUnion (P i)) x)

end ReyZygmund.Sharpness
