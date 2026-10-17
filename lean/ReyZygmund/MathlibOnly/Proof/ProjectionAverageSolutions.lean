import ReyZygmund.MathlibOnly.SupportingStatements
import ReyZygmund.Projection.FiniteSetting
import ReyZygmund.Projection.PreservedAverages
import ReyZygmund.Projection.PartialAverages

/-! # Averages of the finite projection

Weak incomparability makes each removed difference have zero average on an
original rectangle. The product telescope expresses averages of the projected
function using proper subsets of the coordinates.
-/

open BoxIntegral
open scoped BigOperators Classical

namespace ReyZygmund.MathlibOnly

open Geometry Projection

/-- The projection preserves every original average under weak incomparability. -/
theorem projection_preserves_averages : ProjectionPreservesAverages := by
  intro m _hm d hd D I k htop f hs _hpos hf G hG hweak R hR
  choose l hI hcut using htop
  let N := fun i => (l i + k).toNat
  have hfl : ProductLeafConstant I N f :=
    (constantOnBottomRectangles_iff D hI hcut f).mp hf
  let u := finiteInput I N f hfl
  have hu : u.1 = f := finiteInput_eq I N f hfl hs
  have hfinite := finite_of_subset_finiteRectangles D hd hI hcut hG
  let g := hfinite.toFinset
  have hg : (g : Set (Rectangle d)) = G := hfinite.coe_toFinset
  have hgsub : g ⊆ productDescendants I N := by
    intro Q hQ
    have hQG : Q ∈ G := by simpa only [← hg, Finset.mem_coe] using hQ
    have hQd := hG hQG
    rwa [finiteRectangles_eq_productDescendants D hd hI hcut] at hQd
  have hR' : R ∈ g := by simpa only [← hg, Finset.mem_coe] using hR
  have hweak' : ∀ Q ∈ g, ∀ S ∈ g, ¬ ∀ i, Q i < S i := by
    intro Q hQ S hS
    apply hweak Q _ S _
    · simpa only [← hg, Finset.mem_coe] using hQ
    · simpa only [← hg, Finset.mem_coe] using hS
  have hproj : projection D I k G f = (finiteProjectionMap I N g u).1 := by
    simpa only [hu, hg] using projection_eq_finiteProjectionMap D hd hI hcut g u
  have hpreserved := original_averages_preserved_of_weaker_containment
    I N hd g hgsub hweak' R hR'
  calc
    fullAverage R f = (productAverageMap Finset.univ R u).1 := by
      simpa only [hu] using fullAverage_eq_productAverageMap R u
    _ = (productAverageMap Finset.univ R (finiteProjectionMap I N g u)).1 := by
      exact (congrArg (fun T : Module.End ℝ (boundedMeasurableFunctions d) =>
        (T u).1) hpreserved).symm
    _ = fullAverage R (projection D I k G f) := by
      rw [hproj, fullAverage_eq_productAverageMap]

/-- Averages of the projection are signed sums of its averages in fewer coordinates. -/
theorem projection_partial_averages : ProjectionPartialAverages := by
  intro m _hm d hd D I k htop f hs _hpos hf G hG
  dsimp only
  intro R hR x hx
  choose l hI hcut using htop
  let N := fun i => (l i + k).toNat
  have hfl : ProductLeafConstant I N f :=
    (constantOnBottomRectangles_iff D hI hcut f).mp hf
  let u := finiteInput I N f hfl
  have hu : u.1 = f := finiteInput_eq I N f hfl hs
  have hfinite := finite_of_subset_finiteRectangles D hd hI hcut hG
  let g := hfinite.toFinset
  have hg : (g : Set (Rectangle d)) = G := hfinite.coe_toFinset
  have hgsub : g ⊆ productDescendants I N := by
    intro Q hQ
    have hQG : Q ∈ G := by simpa only [← hg, Finset.mem_coe] using hQ
    have hQd := hG hQG
    rwa [finiteRectangles_eq_productDescendants D hd hI hcut] at hQd
  have hR' : R ∈ g := by simpa only [← hg, Finset.mem_coe] using hR
  have hproj : projection D I k G f = (finiteProjectionMap I N g u).1 := by
    simpa only [hu, hg] using projection_eq_finiteProjectionMap D hd hI hcut g u
  have h := finite_projection_partial_averages I N hd g hgsub R hR' u
    (by simpa only [hu] using hfl) (by simpa only [hu] using hs) x hx
  rw [hproj]
  simpa only [fullAverage_eq_productAverageMap, partialAverage_eq_productAverageMap] using h

end ReyZygmund.MathlibOnly
