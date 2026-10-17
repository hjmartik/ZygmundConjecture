import ReyZygmund.MathlibOnly.SupportingStatements
import ReyZygmund.Projection.FiniteSetting
import ReyZygmund.Projection.CrossFiniteSetting
import ReyZygmund.Projection.CrossProjection

/-! # Differences of the finite projection

The cross-projection identity uses coordinate orthogonality, the maximal
partition and one-coordinate telescoping. A bottom factor gives zero by
cancellation. The resulting function identity holds pointwise.
-/

open BoxIntegral
open scoped BigOperators Classical

namespace ReyZygmund.MathlibOnly

open Geometry Projection

/-- Differences of the projection are cross-coordinate averages of the input
differences, including bottom factors and points outside the top rectangle. -/
theorem projection_differences : ProjectionDifferences := by
  intro m _hm d hd D I k htop f hs _hfpos hf G hG j K hK
  choose l hI hcut using htop
  let N := fun i => (l i + k).toNat
  have hfl : ProductLeafConstant I N f :=
    (constantOnBottomRectangles_iff D hI hcut f).mp hf
  let F := finiteInput I N f hfl
  have hF : F.1 = f := finiteInput_eq I N f hfl hs
  have hGfinite := finite_of_subset_finiteRectangles D hd hI hcut hG
  let Gf := hGfinite.toFinset
  have hGset : (Gf : Set (Rectangle d)) = G := hGfinite.coe_toFinset
  have hGdesc : ∀ R ∈ Gf, ∀ i, R i ∈ descendants (I i) (N i) := by
    intro R hR i
    have hRG : R ∈ G := by simpa only [Gf, Set.Finite.mem_toFinset] using hR
    have hRi := hG hRG i
    simpa only [finiteCubes_eq_descendants (D i) (hd i) (hI i) (hcut i),
      Finset.mem_coe] using hRi
  let Q := completePartialRectangle I (Finset.univ.erase j) K
  have hQ : ∀ i, i ≠ j → Q i ∈ descendants (I i) (N i) := by
    intro i hij
    have hi : i ∈ (Finset.univ.erase j : Finset (Fin m)) :=
      Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
    have hKi := hK ⟨i, hi⟩
    rw [finiteCubes_eq_descendants (D i) (hd i) (hI i) (hcut i)] at hKi
    simpa only [Q, completePartialRectangle, dite_eq_left hi, Finset.mem_coe] using hKi
  have hrestrict : (fun i : (Finset.univ.erase j : Finset (Fin m)) => Q i) = K := by
    funext i
    exact completePartialRectangle_selected I (Finset.univ.erase j) K i
  have hDifference (u : boundedMeasurableFunctions d) :
      partialDifference (Finset.univ.erase j) K u.1 =
        (productDifferenceMap (Finset.univ.erase j) Q u).1 := by
    have h := partialDifference_eq_productDifferenceMap (Finset.univ.erase j) Q u
    rwa [hrestrict] at h
  have hDifferenceF : partialDifference (Finset.univ.erase j) K f =
      (productDifferenceMap (Finset.univ.erase j) Q F).1 := by
    simpa only [hF] using hDifference F
  have hprojection : projection D I k G f = (finiteProjectionMap I N Gf F).1 := by
    simpa only [hF, hGset] using projection_eq_finiteProjectionMap D hd hI hcut Gf F
  calc
    partialDifference (Finset.univ.erase j) K (projection D I k G f) =
        (productDifferenceMap (Finset.univ.erase j) Q
          (finiteProjectionMap I N Gf F)).1 := by rw [hprojection, hDifference]
    _ = coordinateCrossAverage j (I j) (N j) (eligibleProjections j Gf Q)
        (productDifferenceMap (Finset.univ.erase j) Q F).1 :=
      finite_cross_projection_descendants I N hd Gf hGdesc f hfl j Q hQ
    _ = crossAverage D I k G j K (partialDifference (Finset.univ.erase j) K f) := by
      rw [← hGset, crossAverage_eq_coordinateCrossAverage D hI hcut Gf j K,
        hDifferenceF]

end ReyZygmund.MathlibOnly
