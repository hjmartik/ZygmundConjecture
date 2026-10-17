import ReyZygmund.Projection.Properties
import ReyZygmund.Geometry.LeafDifference

/-!
# Differences of the projected function at every selected scale

At the smallest selected scale, the difference vanishes by cancellation.
Otherwise every selected cube is interior, and the existing operator identity
and one-coordinate telescope give the cross average. The operator identities in
`CommonProjection` retain their interior hypotheses; the extension here uses
constancy of the input and its projection on the smallest cubes.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Projection

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- A selected cube at the smallest scale makes the product difference vanish. -/
theorem productDifferenceMap_eq_zero_of_leaf
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productRectangle I → F.1 x = 0)
    (A : Finset (Fin m)) (K : ∀ i, Box (Fin (d i)))
    (i : Fin m) (hi : i ∈ A) (hKi : K i ∈ level (I i) (N i)) :
    productDifferenceMap A K F = 0 := by
  have hz : differenceMap i (K i) F = 0 := by
    apply Subtype.ext
    simpa only [differenceMap_apply, ZeroMemClass.coe_zero] using
      coordinateDifference_eq_zero_below_leaf I N F.1 hf hs i (K i) (K i) hKi le_rfl
  have hfactor : productDifferenceMap A K =
      productDifferenceMap (A.erase i) K * differenceMap i (K i) := by
    exact (Finset.noncommProd_erase_mul A hi
      (fun j => differenceMap j (K j))
      (fun j _ k _ hjk => differenceMap_commute j k hjk (K j) (K k))).symm
  rw [hfactor, Module.End.mul_apply, hz, map_zero]

/-- The cross-coordinate identity for every selected descendant,
including cubes of the smallest size. This is a global equality of functions
with the input localized to the top rectangle. -/
theorem finite_cross_projection_descendants
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (hd : ∀ i, 0 < d i) (G : Finset (∀ i, Box (Fin (d i))))
    (hG : ∀ J ∈ G, ∀ i, J i ∈ descendants (I i) (N i))
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (j : Fin m) (K : ∀ i, Box (Fin (d i)))
    (hK : ∀ i, i ≠ j → K i ∈ descendants (I i) (N i)) :
    (productDifferenceMap (Finset.univ.erase j) K
      (finiteProjectionMap I N G (finiteInput I N f hf))).1 =
        coordinateCrossAverage j (I j) (N j) (eligibleProjections j G K)
          (productDifferenceMap (Finset.univ.erase j) K (finiteInput I N f hf)).1 := by
  by_cases hinterior : ∀ i, i ≠ j → K i ∈ interior (I i) (N i)
  · exact finite_cross_projection I N hd G hG f hf j K hinterior
  · push Not at hinterior
    obtain ⟨i, hij, hnot⟩ := hinterior
    have hleaf : K i ∈ level (I i) (N i) := by
      obtain ⟨k, hk, hKk⟩ := mem_descendants.mp (hK i hij)
      have hkN : k = N i := le_antisymm hk (le_of_not_gt (fun hlt =>
        hnot (mem_interior.mpr ⟨k, hlt, hKk⟩)))
      simpa only [hkN] using hKk
    let F := finiteInput I N f hf
    have hF : ProductLeafConstant I N F.1 := productLeafConstant_indicator hf
    have hFs : ∀ x, x ∉ productRectangle I → F.1 x = 0 :=
      fun x hx => Set.indicator_of_notMem hx f
    have hprojection := finiteProjectionMap_productStep_closure I N G F hF hFs
    have hi : i ∈ (Finset.univ.erase j : Finset (Fin m)) :=
      Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
    have hinputZero := productDifferenceMap_eq_zero_of_leaf I N F hF hFs
      (Finset.univ.erase j) K i hi hleaf
    have hprojectionZero := productDifferenceMap_eq_zero_of_leaf I N
      (finiteProjectionMap I N G F) hprojection.1 hprojection.2
      (Finset.univ.erase j) K i hi hleaf
    change (productDifferenceMap (Finset.univ.erase j) K
      (finiteProjectionMap I N G F)).1 =
        coordinateCrossAverage j (I j) (N j) (eligibleProjections j G K)
          (productDifferenceMap (Finset.univ.erase j) K F).1
    rw [hprojectionZero, hinputZero]
    simpa only [map_zero] using
      crossAverageMap_apply j (I j) (N j) (eligibleProjections j G K)
        (0 : boundedMeasurableFunctions d)

end ReyZygmund.Projection
