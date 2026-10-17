import ReyZygmund.MathlibOnly.Proof.ProjectionAverageSolutions
import ReyZygmund.Projection.AveragingFiniteSetting
import ReyZygmund.Projection.AveragingGeometry

/-! # Geometry and representation on the enlarged family

Adding the averaging rectangles removes no further difference indices and
preserves weak incomparability. The representation then follows by applying
preserved averages and the formula in fewer coordinates to the enlarged family.
-/

open BoxIntegral
open scoped BigOperators Classical

namespace ReyZygmund.MathlibOnly

open Geometry Projection

/-- The averaging enlargement has the same projection, and is weakly
incomparable whenever the original family is. -/
theorem averaging_family_geometry : AveragingFamilyGeometry := by
  intro m _hm d hd D I k htop f hs _hpos hf G hG
  dsimp only
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
    intro R hR
    have hRG : R ∈ G := by simpa only [← hg, Finset.mem_coe] using hR
    have hRd := hG hRG
    rwa [finiteRectangles_eq_productDescendants D hd hI hcut] at hRd
  have hB : averagingRectangles D I k G =
      (Projection.averagingRectangles I N g : Set (Rectangle d)) := by
    simpa only [hg] using averagingRectangles_eq_finiteAveragingRectangles D hd hI hcut g
  have hhat :
      ((g ∪ Projection.averagingRectangles I N g : Finset (Rectangle d)) :
        Set (Rectangle d)) = G ∪ averagingRectangles D I k G := by
    rw [Finset.coe_union, hg, ← hB]
  constructor
  · calc
      projection D I k (G ∪ averagingRectangles D I k G) f =
          (finiteProjectionMap I N (g ∪ Projection.averagingRectangles I N g) u).1 := by
            simpa only [hu, hhat] using projection_eq_finiteProjectionMap
              D hd hI hcut (g ∪ Projection.averagingRectangles I N g) u
      _ = (finiteProjectionMap I N g u).1 := by
        rw [finiteProjectionMap_union_averagingRectangles I N hd g]
      _ = projection D I k G f := by
        symm
        simpa only [hu, hg] using projection_eq_finiteProjectionMap D hd hI hcut g u
  · intro hweak
    have hweak' : WeaklyIncomparable (g : Set (Rectangle d)) := by
      simpa only [hg] using hweak
    simpa only [hhat] using
      weaklyIncomparable_union_averagingRectangles I N hd g hgsub hweak'

/-- On the enlarged family, preserve the input average and then express the
projected average using every proper subset of the coordinates. -/
theorem representation_of_averages : RepresentationOfAverages := by
  intro m hm d hd D I k htop f hs hpos hf G hG hweak
  dsimp only
  intro R hR x hx
  have hhat : G ∪ averagingRectangles D I k G ⊆ finiteRectangles D I k := by
    intro Q hQ
    rcases hQ with hQ | hQ
    · exact hG hQ
    · exact hQ.1
  obtain ⟨hprojection, hgeometry⟩ :=
    averaging_family_geometry m hm d hd D I k htop f hs hpos hf G hG
  have hpreserved := projection_preserves_averages m hm d hd D I k htop
    f hs hpos hf (G ∪ averagingRectangles D I k G) hhat (hgeometry hweak) R hR
  have hpartial := projection_partial_averages m hm d hd D I k htop
    f hs hpos hf (G ∪ averagingRectangles D I k G) hhat R hR x hx
  rw [hprojection] at hpreserved hpartial
  exact (congrFun hpreserved x).trans hpartial

end ReyZygmund.MathlibOnly
