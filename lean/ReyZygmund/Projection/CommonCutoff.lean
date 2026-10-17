import ReyZygmund.Geometry.SourceCutoff
import ReyZygmund.Projection.GridProjection

/-!
# A common smallest scale in the given grids

The common smallest scale has generation `k`, while the top cube in
coordinate `i` has generation `n i ≤ k`.
Its finite depth is therefore `(k - n i).toNat`.

`source_productDescendants_iff` and `source_productInterior_iff` identify the
grid rectangles with sides respectively at least and strictly greater
than `2^(-k)`. `source_productLeafConstant_iff` identifies the pointwise
constancy assumption. These identities give finite-family membership and a
finite step input.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

open ReyZygmund.MathlibOnly (CubeGrid gridRectangles)

namespace ReyZygmund.Projection

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- A family with the prescribed smallest scale is finite and can be represented
by a `Finset`. -/
theorem common_cutoff_family_finite
    (hd : ∀ i, 0 < d i) (D : ∀ i, CubeGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubesAtGeneration (n i))
    (hnk : ∀ i, n i ≤ k) (G : Set (∀ i, Box (Fin (d i))))
    (hG : ∀ R ∈ G, R ∈ gridRectangles D ∧ productRectangle R ⊆ productRectangle I ∧
      ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u) :
    G.Finite := by
  apply (productDescendants I (fun i => (k - n i).toNat)).finite_toSet.subset
  intro R hR
  exact (source_productDescendants_iff hd D n k I hI hnk R).mpr (hG R hR)

/-- The full-grid projection with a common smallest scale.
Constancy on the smallest cubes produces a bounded measurable finite input equal
everywhere to `f`. The full-grid expression has a finitely supported difference
sum and equals the finite projection, which preserves that constancy and support. -/
theorem source_grid_projection
    (hd : ∀ i, 0 < d i) (D : ∀ i, CubeGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubesAtGeneration (n i))
    (hnk : ∀ i, n i ≤ k) (G : Finset (∀ i, Box (Fin (d i))))
    (hG : ∀ R ∈ G, R ∈ gridRectangles D ∧ productRectangle R ⊆ productRectangle I ∧
      ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u)
    (f : ProductPoint d → ℝ) (hs : ∀ x, x ∉ productRectangle I → f x = 0)
    (hf : ∀ R, (R ∈ gridRectangles D ∧ productRectangle R ⊆ productRectangle I ∧
      ∀ i u, (R i).upper u - (R i).lower u = (2 : ℝ) ^ (-k)) →
      ∀ x ∈ productRectangle R, ∀ y ∈ productRectangle R, f x = f y) :
    let N := fun i => (k - n i).toNat
    ∃ hleaf : ProductLeafConstant I N f,
      let u := finiteInput I N f hleaf
      u.1 = f ∧
      (Function.support (fun L : {L : ∀ i, Box (Fin (d i)) //
          L ∈ gridRectangles D ∧ ∃ J ∈ G, productRectangle L ⊆ productRectangle J} =>
        rawProductDifference L.1 f)).Finite ∧
      ((finiteProjectionMap I N G u).1 = f -
        ∑' L : {L : ∀ i, Box (Fin (d i)) //
          L ∈ gridRectangles D ∧ ∃ J ∈ G, productRectangle L ⊆ productRectangle J},
          rawProductDifference L.1 f) ∧
      ProductLeafConstant I N (finiteProjectionMap I N G u).1 ∧
      ∀ x, x ∉ productRectangle I → (finiteProjectionMap I N G u).1 x = 0 := by
  let N := fun i => (k - n i).toNat
  have hGd : G ⊆ productDescendants I N := by
    intro R hR
    exact (source_productDescendants_iff hd D n k I hI hnk R).mpr (hG R hR)
  have hleaf : ProductLeafConstant I N f :=
    (source_productLeafConstant_iff hd D n k I hI hnk f).mpr hf
  let u := finiteInput I N f hleaf
  have hu : u.1 = f := finiteInput_eq I N f hleaf hs
  have hul : ProductLeafConstant I N u.1 := by rw [hu]; exact hleaf
  have hus : ∀ x, x ∉ productRectangle I → u.1 x = 0 := by rw [hu]; exact hs
  have hsum := grid_removedDifference_hasSum hd D n I N hI G hGd u hul hus
  have hgrid := grid_projection_eq_tsum hd D n I N hI G hGd u hul hus
  simp only [hu] at hsum hgrid
  have hprojection := finiteProjectionMap_productStep_closure I N G u hul hus
  exact ⟨hleaf, hu, hsum.1, hgrid, hprojection.1, hprojection.2⟩

end ReyZygmund.Projection
