import ReyZygmund.Geometry.SourceCutoff
import ReyZygmund.Projection.GridProjection

/-!
# A common smallest scale in the given grids

The common smallest scale has generation `k`, while the top cube in
coordinate `i` has generation `n i ≤ k`.
Its finite depth is therefore `(k - n i).toNat`.

`source_productDescendants_iff` and `source_productInterior_iff` identify the
grid rectangles with sides respectively at least and strictly greater
than `2^(-k)`. `source_productLeafConstant_iff` identifies the paper's pointwise
constancy assumption. We use these dictionaries below to derive finite-family
membership and the finite input without changing grids.
The smallest cubes have absolute generation `k`.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Projection

open Geometry

/-- The smallest cubes in the finite construction are precisely the cubes
of absolute generation `k` contained in the supplied root. This includes the
zero-depth case `n = k`. -/
theorem common_cutoff_leaves_iff {e : ℕ}
    (D : DyadicGrid e) (n k : ℤ) (I Q : Box (Fin e))
    (hI : I ∈ D.cubes n) (hnk : n ≤ k) :
    Q ∈ leaves I (k - n).toNat ↔ Q ∈ D.cubes k ∧ Q ≤ I := by
  have hcut : n + ((k - n).toNat : ℤ) = k := by omega
  rw [mem_leaves, D.mem_level_iff hI, hcut]

variable {m : ℕ} {d : Fin m → ℕ}

/-- The product leaves have the same absolute generation in every coordinate,
although their depths below the supplied roots can differ. -/
theorem common_cutoff_productLeaves_iff
    (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubes (n i))
    (hnk : ∀ i, n i ≤ k) (R : ∀ i, Box (Fin (d i))) :
    R ∈ productLeaves I (fun i => (k - n i).toNat) ↔
      (∀ i, R i ∈ (D i).cubes k) ∧ productBox R ⊆ productBox I := by
  constructor
  · intro hR
    have hc (i : Fin m) :=
      (common_cutoff_leaves_iff (D i) (n i) k (I i) (R i) (hI i) (hnk i)).mp
        (Fintype.mem_piFinset.mp hR i)
    exact ⟨fun i => (hc i).1,
      (productBox_subset_iff R I).mpr (fun i => (hc i).2)⟩
  · rintro ⟨hR, hRI⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    exact (common_cutoff_leaves_iff (D i) (n i) k (I i) (R i) (hI i) (hnk i)).mpr
      ⟨hR i, (productBox_subset_iff R I).mp hRI i⟩

/-- A family with the prescribed smallest scale is finite, so
representing it by a `Finset` adds no
finiteness assumption. -/
theorem common_cutoff_family_finite
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubes (n i))
    (hnk : ∀ i, n i ≤ k) (G : Set (∀ i, Box (Fin (d i))))
    (hG : ∀ R ∈ G, R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
      ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u) :
    G.Finite := by
  apply (productDescendants I (fun i => (k - n i).toNat)).finite_toSet.subset
  intro R hR
  exact (source_productDescendants_iff hd D n k I hI hnk R).mpr (hG R hR)

/-- The full-grid projection with a common smallest scale.
Constancy on the smallest cubes produces a bounded measurable finite input equal
everywhere to `f`. The full-grid expression has a finitely supported difference
sum and equals the finite projection, which preserves that constancy and support.
The family may be empty; positivity and incomparability are not needed here. -/
theorem source_grid_projection
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubes (n i))
    (hnk : ∀ i, n i ≤ k) (G : Finset (∀ i, Box (Fin (d i))))
    (hG : ∀ R ∈ G, R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
      ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u)
    (f : ProductPoint d → ℝ) (hs : ∀ x, x ∉ productBox I → f x = 0)
    (hf : ∀ R, (R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
      ∀ i u, (R i).upper u - (R i).lower u = (2 : ℝ) ^ (-k)) →
      ∀ x ∈ productBox R, ∀ y ∈ productBox R, f x = f y) :
    let N := fun i => (k - n i).toNat
    ∃ hleaf : ProductLeafConstant I N f,
      let u := finiteInput I N f hleaf
      u.1 = f ∧
      (Function.support (fun L : {L : ∀ i, Box (Fin (d i)) //
          L ∈ gridRectangles D ∧ ∃ J ∈ G, productBox L ⊆ productBox J} =>
        rawProductDifference L.1 f)).Finite ∧
      ((finiteProjectionMap I N G u).1 = f -
        ∑' L : {L : ∀ i, Box (Fin (d i)) //
          L ∈ gridRectangles D ∧ ∃ J ∈ G, productBox L ⊆ productBox J},
          rawProductDifference L.1 f) ∧
      ProductLeafConstant I N (finiteProjectionMap I N G u).1 ∧
      ∀ x, x ∉ productBox I → (finiteProjectionMap I N G u).1 x = 0 := by
  let N := fun i => (k - n i).toNat
  have hGd : G ⊆ productDescendants I N := by
    intro R hR
    exact (source_productDescendants_iff hd D n k I hI hnk R).mpr (hG R hR)
  have hleaf : ProductLeafConstant I N f :=
    (source_productLeafConstant_iff hd D n k I hI hnk f).mpr hf
  let u := finiteInput I N f hleaf
  have hu : u.1 = f := by
    funext x
    by_cases hx : x ∈ productBox I
    · exact Set.indicator_of_mem hx f
    · change (productBox I).indicator f x = f x
      rw [Set.indicator_of_notMem hx, hs x hx]
  have hul : ProductLeafConstant I N u.1 := by rw [hu]; exact hleaf
  have hus : ∀ x, x ∉ productBox I → u.1 x = 0 := by rw [hu]; exact hs
  have hsum := grid_removedDifference_hasSum hd D n I N hI G hGd u hul hus
  have hgrid := grid_projection_eq_tsum hd D n I N hI G hGd u hul hus
  simp only [hu] at hsum hgrid
  have hprojection := finiteProjectionMap_productStep_closure I N G u hul hus
  exact ⟨hleaf, hu, hsum.1, hgrid, hprojection.1, hprojection.2⟩

end ReyZygmund.Projection
