import ReyZygmund.Geometry.SourceCutoff

/-! # Averaging rectangles at a common smallest scale

The finite partition construction applies to the paper's common smallest side
length and its set-theoretic incomparability condition. The containing top
rectangle is the one supplied in the statement.
-/

open BoxIntegral
open scoped Classical

namespace ReyZygmund.Projection

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- Source membership in the averaging family. No incomparability or
membership hypothesis on the original family is needed for this definition. -/
theorem source_mem_averagingRectangles
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubes (n i))
    (hnk : ∀ i, n i ≤ k) (G : Finset (∀ i, Box (Fin (d i))))
    (R : ∀ i, Box (Fin (d i))) :
    R ∈ averagingRectangles I (fun i => (k - n i).toNat) G ↔
      (R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
        ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u) ∧
        ∃ j : Fin m, R j ∈ partitionCubes (I j) (k - n j).toNat
          (eligibleProjections j G R) := by
  rw [averagingRectangles, Finset.mem_filter,
    source_productDescendants_iff hd D n k I hI hnk R]

/-- Every coordinate of every original incomparable rectangle is a partition
cube, under the paper's grid, side and set-containment hypotheses. -/
theorem source_original_mem_partitionCubes
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubes (n i))
    (hnk : ∀ i, n i ≤ k) (G : Finset (∀ i, Box (Fin (d i))))
    (hG : ∀ R ∈ G, R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
      ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → R = S)
    (R : ∀ i, Box (Fin (d i))) (hR : R ∈ G) (j : Fin m) :
    R j ∈ partitionCubes (I j) (k - n j).toNat (eligibleProjections j G R) := by
  have hGd : G ⊆ productDescendants I (fun i => (k - n i).toNat) := by
    intro S hS
    exact (source_productDescendants_iff hd D n k I hI hnk S).mpr (hG S hS)
  exact original_mem_partitionCubes I (fun i => (k - n i).toNat) G hGd
    (fun S hS T hT hST => hinc S hS T hT ((productBox_subset_iff S T).mpr hST))
    R hR j

/-- The original family is contained in the paper's averaging family. The
positive number of coordinates is used only to supply its existential index. -/
theorem source_original_subset_averagingRectangles
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubes (n i))
    (hnk : ∀ i, n i ≤ k) (G : Finset (∀ i, Box (Fin (d i))))
    (hG : ∀ R ∈ G, R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
      ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → R = S)
    (hm : 0 < m) : G ⊆ averagingRectangles I (fun i => (k - n i).toNat) G := by
  have hGd : G ⊆ productDescendants I (fun i => (k - n i).toNat) := by
    intro R hR
    exact (source_productDescendants_iff hd D n k I hI hnk R).mpr (hG R hR)
  exact original_subset_averagingRectangles hm I (fun i => (k - n i).toNat) G hGd
    (fun R hR S hS hRS => hinc R hR S hS ((productBox_subset_iff R S).mpr hRS))

end ReyZygmund.Projection
