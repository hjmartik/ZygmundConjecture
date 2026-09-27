import ReyZygmund.Projection.SourceAveraging
import ReyZygmund.Projection.Representation
import ReyZygmund.Geometry.ProductMean
import ReyZygmund.Geometry.ProductIntegrability

/-! # The representation at a common smallest scale

A member of the nonempty original family ensures that every top cube reaches the
specified smallest scale. Constancy at that scale gives the finite step function,
equal pointwise to the zero-extended input. The representation identities use
normalized Lebesgue averages on the averaging rectangles.


-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Projection

open Geometry

/-- The representation under the paper's input hypotheses. Nonemptiness of the family
gives compatibility with the smallest scale. Boundedness, measurability and
integrability of the finite representative are proved from these hypotheses. -/
theorem source_representation
    {m : ℕ} {d : Fin m → ℕ} (_hm : 2 ≤ m) (hd : ∀ i, 0 < d i)
    (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubes (n i))
    (G : Finset (∀ i, Box (Fin (d i)))) (hne : G.Nonempty)
    (hG : ∀ R ∈ G, R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
      ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u)
    (_hinc : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → R = S)
    (f : ProductPoint d → ℝ) (hs : ∀ x, x ∉ productBox I → f x = 0)
    (_hfpos : ∀ x ∈ productBox I, 0 < f x)
    (hf : ∀ R, (R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
      ∀ i u, (R i).upper u - (R i).lower u = (2 : ℝ) ^ (-k)) →
      ∀ x ∈ productBox R, ∀ y ∈ productBox R, f x = f y) :
    let N := fun i => (k - n i).toNat
    ∃ hleaf : ProductLeafConstant I N f,
      let u := finiteInput I N f hleaf
      let F := finiteProjectionMap I N G u
      u.1 = f ∧ IntegrableOn f (productBox I) volume ∧
      IntegrableOn F.1 (productBox I) volume ∧
      ∀ R ∈ averagingRectangles I N G,
        (∫ y in productBox R, F.1 y) / volume.real (productBox R) =
          (∫ y in productBox R, f y) / volume.real (productBox R) ∧
        ∀ x ∈ productBox R,
          (∫ y in productBox R, f y) / volume.real (productBox R) =
            ∑ B ∈ ((Finset.univ : Finset (Fin m)).powerset.erase Finset.univ),
              (-1 : ℝ) ^ (m + 1 + B.card) * (productAverageMap B R F).1 x := by
  have hnk : ∀ i, n i ≤ k :=
    (source_cutoff_or_empty hd D n k I hI G hG).resolve_right
      (Finset.nonempty_iff_ne_empty.mp hne)
  let N := fun i => (k - n i).toNat
  have hleaf : ProductLeafConstant I N f :=
    (source_productLeafConstant_iff hd D n k I hI hnk f).mpr hf
  let u := finiteInput I N f hleaf
  let F := finiteProjectionMap I N G u
  have hu : u.1 = f := by
    funext x
    by_cases hx : x ∈ productBox I
    · exact Set.indicator_of_mem hx f
    · change (productBox I).indicator f x = f x
      rw [Set.indicator_of_notMem hx, hs x hx]
  have hul : ProductLeafConstant I N u.1 := by rw [hu]; exact hleaf
  have hus : ∀ x, x ∉ productBox I → u.1 x = 0 := by rw [hu]; exact hs
  have hF := finiteProjectionMap_productStep_closure I N G u hul hus
  refine ⟨hleaf, hu, integrableOn_productLeafConstant I N f hleaf,
    integrableOn_productLeafConstant I N F.1 hF.1, ?_⟩
  intro R hR
  have hpoint (x : ProductPoint d) (hx : x ∈ productBox R) :
      (∫ y in productBox R, F.1 y) / volume.real (productBox R) =
        (∫ y in productBox R, f y) / volume.real (productBox R) ∧
      (∫ y in productBox R, f y) / volume.real (productBox R) =
        ∑ B ∈ ((Finset.univ : Finset (Fin m)).powerset.erase Finset.univ),
          (-1 : ℝ) ^ (m + 1 + B.card) * (productAverageMap B R F).1 x := by
    have hmeanU : (productAverageMap Finset.univ R u).1 x =
        (∫ y in productBox R, f y) / volume.real (productBox R) := by
      rw [productAverageMap_univ_eq_integral, Set.indicator_of_mem hx, hu]
    have hmeanF : (productAverageMap Finset.univ R F).1 x =
        (∫ y in productBox R, F.1 y) / volume.real (productBox R) := by
      rw [productAverageMap_univ_eq_integral, Set.indicator_of_mem hx]
    have hpres : (productAverageMap Finset.univ R F).1 x =
        (productAverageMap Finset.univ R u).1 x := by
      exact congrArg (fun T : Module.End ℝ (boundedMeasurableFunctions d) => (T u).1 x)
        (averagingRectangles_preserved I N hd G R hR)
    refine ⟨hmeanF.symm.trans (hpres.trans hmeanU), ?_⟩
    exact hmeanU.symm.trans (finite_representation I N hd G R hR u hul hus x hx)
  exact ⟨(hpoint (fun i => (R i).upper)
    ((mem_productBox R _).mpr (fun i => (R i).upper_mem))).1,
    fun x hx => (hpoint x hx).2⟩

end ReyZygmund.Projection
