import ReyZygmund.Projection.LocalProductExpansion
import ReyZygmund.ToMathlib.Algebra.BigOperators.Powerset

/-! # Averages of the projection in fewer coordinates

On a rectangle in the original family, the local product telescope vanishes:
every full difference in its sum is removed by the projection. Separating the
full set of coordinates in the signed expansion expresses the full average
using the proper subsets, including the empty subset.
-/

open BoxIntegral
open scoped BigOperators Classical

namespace ReyZygmund.Projection

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- The full average of the projected function is a signed sum of its averages
in fewer coordinates, pointwise on each member of the original family. -/
theorem finite_projection_partial_averages
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (R : ∀ i, Box (Fin (d i))) (hR : R ∈ G)
    (u : boundedMeasurableFunctions d) (hu : ProductLeafConstant I N u.1)
    (hs : ∀ x, x ∉ productRectangle I → u.1 x = 0)
    (x : ProductPoint d) (hx : x ∈ productRectangle R) :
    let F := finiteProjectionMap I N G u
    (productAverageMap Finset.univ R F).1 x =
      ∑ B ∈ (Finset.univ : Finset (Fin m)).ssubsets,
        (-1 : ℝ) ^ (m + 1 + B.card) * (productAverageMap B R F).1 x := by
  let F := finiteProjectionMap I N G u
  have hc := finiteProjectionMap_productStep_closure I N G u hu hs
  have hzero :
      (∑ L ∈ (productInterior I N).filter (fun L => ∀ i, L i ≤ R i),
        (productDifferenceMap Finset.univ L F).1 x) = 0 := by
    apply Finset.sum_eq_zero
    intro L hL
    obtain ⟨hLi, hLR⟩ := Finset.mem_filter.mp hL
    have hremoved : L ∈ removedIndices I N G :=
      Finset.mem_filter.mpr ⟨hLi, R, hR, hLR⟩
    have h := congrArg (fun T : Module.End ℝ (boundedMeasurableFunctions d) => (T u).1 x)
      (productDifferenceMap_mul_finiteProjectionMap I N hd G L hremoved)
    simpa [F, Module.End.mul_apply] using h
  have hexp := local_product_expansion I N hd R (mem_productDescendants.mp (hG hR))
    F hc.1 hc.2 x hx
  have hfull :
      (∑ B ∈ (Finset.univ : Finset (Fin m)).powerset,
        (-1 : ℝ) ^ B.card * (productAverageMap B R F).1 x) = 0 :=
    hexp.symm.trans hzero
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.eq_sum_ssubsets_of_sum_powerset_eq_zero
      (Finset.univ : Finset (Fin m)) (fun B => (productAverageMap B R F).1 x) hfull

end ReyZygmund.Projection
