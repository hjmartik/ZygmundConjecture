import ReyZygmund.Geometry.LeafDifference
import ReyZygmund.Geometry.RawDifferenceBridge
import ReyZygmund.Geometry.GridOrder
import ReyZygmund.Geometry.ProductContainment
import ReyZygmund.Projection.Properties
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! # The common projection on the full grids

Cancellation on and below the smallest cubes makes the removed-difference sum
over the full grids finitely supported. Subtracting this sum from the input gives
the finite projection, which annihilates every removed difference, including
those at smaller scales.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Projection

open Geometry

/-- Every contained grid cube below the smallest retained scale has an ancestor at that scale. -/
theorem grid_cutoff_ancestor {e : ℕ} (D : DyadicGrid e) {n a : ℤ}
    (I Q : Box (Fin e)) (N : ℕ) (hI : I ∈ D.cubes n) (hQ : Q ∈ D.cubes a)
    (hQI : Q ≤ I) (hcut : n + (N : ℤ) ≤ a) :
    ∃ P, P ∈ level I N ∧ Q ≤ P := by
  obtain ⟨P, hP, hQP⟩ := D.exists_ancestor hQ hcut
  exact ⟨P, D.mem_level_of_mem_point hI hP (hQI Q.upper_mem) (hQP Q.upper_mem), hQP⟩

variable {m : ℕ} {d : Fin m → ℕ}

/-- One at/below-cutoff coordinate makes the full difference zero.
The other coordinate boxes need no grid or finite-depth restriction. -/
theorem rawProductDifference_eq_zero_of_cutoff
    (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (hI : ∀ j, I j ∈ (D j).cubes (n j))
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (L : ∀ i, Box (Fin (d i))) (i : Fin m) (a : ℤ)
    (hL : L i ∈ (D i).cubes a) (hLI : L i ≤ I i) (hcut : n i + (N i : ℤ) ≤ a) :
    rawProductDifference L F.1 = 0 := by
  obtain ⟨P, hP, hLP⟩ := grid_cutoff_ancestor (D i) (I i) (L i) (N i) (hI i) hL hLI hcut
  have hz : differenceMap i (L i) F = 0 := by
    apply Subtype.ext
    simpa only [differenceMap_apply, ZeroMemClass.coe_zero] using
      coordinateDifference_eq_zero_below_leaf I N F.1 hf hs i P (L i) hP hLP
  have hfactor : productDifferenceMap Finset.univ L =
      productDifferenceMap (Finset.univ.erase i) L * differenceMap i (L i) := by
    exact (Finset.noncommProd_erase_mul Finset.univ (Finset.mem_univ i)
      (fun j => differenceMap j (L j))
      (fun j _ k _ hjk => differenceMap_commute j k hjk (L j) (L k))).symm
  have hfull : productDifferenceMap Finset.univ L F = 0 := by
    rw [hfactor, Module.End.mul_apply, hz, map_zero]
  rw [rawProductDifference_eq_productDifferenceMap L F]
  simpa only [ZeroMemClass.coe_zero] using
    congrArg (fun G : boundedMeasurableFunctions d => G.1) hfull

private theorem grid_generation_le_of_le {e : ℕ} (he : 0 < e)
    (D : DyadicGrid e) {a b : ℤ} {Q R : Box (Fin e)}
    (hQ : Q ∈ D.cubes a) (hR : R ∈ D.cubes b) (hQR : Q ≤ R) : b ≤ a := by
  let i : Fin e := ⟨0, he⟩
  have hb := Box.le_iff_bounds.mp hQR
  have hw : Q.upper i - Q.lower i ≤ R.upper i - R.lower i :=
    sub_le_sub (hb.2 i) (hb.1 i)
  rw [D.width a Q hQ i, D.width b R hR i] at hw
  have hneg := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hw
  omega

private theorem grid_mem_interior_of_generation_lt {e : ℕ} (he : 0 < e)
    (D : DyadicGrid e) {n a : ℤ} (I Q : Box (Fin e)) (N : ℕ)
    (hI : I ∈ D.cubes n) (hQ : Q ∈ D.cubes a) (hQI : Q ≤ I)
    (hlt : a < n + (N : ℤ)) : Q ∈ interior I N := by
  have hna := grid_generation_le_of_le he D hQ hI hQI
  have hindex : n + ((a - n).toNat : ℤ) = a := by omega
  refine mem_interior.mpr ⟨(a - n).toNat, by omega, ?_⟩
  exact (D.mem_level_iff hI).mpr ⟨by simpa only [hindex] using hQ, hQI⟩

private theorem grid_removed_cases
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (hI : ∀ j, I j ∈ (D j).cubes (n j))
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (L : ∀ i, Box (Fin (d i))) (hL : L ∈ gridRectangles D)
    (hremoved : ∃ J ∈ G, productBox L ⊆ productBox J) :
    L ∈ removedIndices I N G ∨
      ∃ (i : Fin m) (a : ℤ), L i ∈ (D i).cubes a ∧ L i ≤ I i ∧ n i + (N i : ℤ) ≤ a := by
  obtain ⟨J, hJ, hLJ⟩ := hremoved
  have hcoord := (productBox_subset_iff L J).mp hLJ
  have hLI (i : Fin m) : L i ≤ I i :=
    (hcoord i).trans (le_of_mem_descendants (mem_productDescendants.mp (hG hJ) i))
  choose a ha using hL
  by_cases hcut : ∃ i, n i + (N i : ℤ) ≤ a i
  · obtain ⟨i, hi⟩ := hcut
    exact Or.inr ⟨i, a i, ha i, hLI i, hi⟩
  · apply Or.inl
    apply Finset.mem_filter.mpr
    refine ⟨mem_productInterior.mpr ?_, J, hJ, hcoord⟩
    intro i
    exact grid_mem_interior_of_generation_lt (hd i) (D i) (I i) (L i) (N i)
      (hI i) (ha i) (hLI i) (lt_of_not_ge (fun hi => hcut ⟨i, hi⟩))

private theorem removedIndices_grid_mem
    (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (hI : ∀ j, I j ∈ (D j).cubes (n j))
    (G : Finset (∀ i, Box (Fin (d i))))
    (L : ∀ i, Box (Fin (d i))) (hL : L ∈ removedIndices I N G) :
    L ∈ gridRectangles D ∧ ∃ J ∈ G, productBox L ⊆ productBox J := by
  obtain ⟨hinterior, J, hJ, hLJ⟩ := Finset.mem_filter.mp hL
  refine ⟨?_, J, hJ, (productBox_subset_iff L J).mpr hLJ⟩
  intro i
  obtain ⟨k, _, hk⟩ := mem_interior.mp (mem_productInterior.mp hinterior i)
  exact ⟨n i + (k : ℤ), (D i).mem_cubes_of_mem_level (hI i) hk⟩

private theorem grid_removed_zero_of_not_mem
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (hI : ∀ j, I j ∈ (D j).cubes (n j))
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (L : ∀ i, Box (Fin (d i))) (hL : L ∈ gridRectangles D)
    (hremoved : ∃ J ∈ G, productBox L ⊆ productBox J)
    (hnot : L ∉ removedIndices I N G) : rawProductDifference L F.1 = 0 := by
  rcases grid_removed_cases hd D n I N hI G hG L hL hremoved with hmem | hcut
  · exact (hnot hmem).elim
  · obtain ⟨i, a, hLi, hLI, hcut⟩ := hcut
    exact rawProductDifference_eq_zero_of_cutoff D n I N hI F hf hs L i a hLi hLI hcut

/-- The first source projection sum has finite support and a
function-valued sum. The subtype counts each removed rectangle once. -/
theorem grid_removedDifference_hasSum
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (hI : ∀ j, I j ∈ (D j).cubes (n j))
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) :
    (Function.support (fun L : {L : ∀ i, Box (Fin (d i)) //
        L ∈ gridRectangles D ∧ ∃ J ∈ G, productBox L ⊆ productBox J} =>
      rawProductDifference L.1 F.1)).Finite ∧
    HasSum (fun L : {L : ∀ i, Box (Fin (d i)) //
        L ∈ gridRectangles D ∧ ∃ J ∈ G, productBox L ⊆ productBox J} =>
      rawProductDifference L.1 F.1) (F.1 - (finiteProjectionMap I N G F).1) := by
  let U : Set (∀ i, Box (Fin (d i))) :=
    {L | L ∈ gridRectangles D ∧ ∃ J ∈ G, productBox L ⊆ productBox J}
  let f : (∀ i, Box (Fin (d i))) → (ProductPoint d → ℝ) :=
    fun L => rawProductDifference L F.1
  change (Function.support (fun L : U => f L.1)).Finite ∧
    HasSum (fun L : U => f L.1) (F.1 - (finiteProjectionMap I N G F).1)
  have hmem (L : ∀ i, Box (Fin (d i))) (hL : L ∈ removedIndices I N G) : L ∈ U :=
    removedIndices_grid_mem D n I N hI G L hL
  have hzero (L : ∀ i, Box (Fin (d i))) (hL : L ∈ U)
      (hnot : L ∉ removedIndices I N G) : f L = 0 :=
    grid_removed_zero_of_not_mem hd D n I N hI G hG F hf hs L hL.1 hL.2 hnot
  have hsupport : Function.support (fun L : U => f L.1) ⊆
      (Subtype.val ⁻¹' (↑(removedIndices I N G) : Set (∀ i, Box (Fin (d i))))) := by
    intro L hL
    change L.1 ∈ removedIndices I N G
    by_contra hnot
    exact hL (hzero L.1 L.2 hnot)
  have hfinite : (Subtype.val ⁻¹' (↑(removedIndices I N G) :
      Set (∀ i, Box (Fin (d i)))) : Set U).Finite :=
    (removedIndices I N G).finite_toSet.preimage Subtype.val_injective.injOn
  refine ⟨hfinite.subset hsupport, ?_⟩
  have hvanish : ∀ L ∉ removedIndices I N G, U.indicator f L = 0 := by
    intro L hnot
    by_cases hL : L ∈ U
    · rw [Set.indicator_of_mem hL]
      exact hzero L hL hnot
    · exact Set.indicator_of_notMem hL f
  have hsum : HasSum (U.indicator f)
      (∑ L ∈ removedIndices I N G, U.indicator f L) :=
    hasSum_sum_of_ne_finset_zero hvanish
  have hvalue : (∑ L ∈ removedIndices I N G, U.indicator f L) =
      F.1 - (finiteProjectionMap I N G F).1 := by
    rw [finiteProjectionMap_apply, sub_sub_cancel]
    apply Finset.sum_congr rfl
    intro L hL
    rw [Set.indicator_of_mem (hmem L hL)]
    exact rawProductDifference_eq_productDifferenceMap L F
  rw [hvalue] at hsum
  exact hasSum_subtype_iff_indicator.mpr hsum

/-- The two source formulas for the projection agree on the unchanged grids. -/
theorem grid_projection_eq_tsum
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (hI : ∀ j, I j ∈ (D j).cubes (n j))
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) :
    (finiteProjectionMap I N G F).1 = F.1 -
      ∑' L : {L : ∀ i, Box (Fin (d i)) //
        L ∈ gridRectangles D ∧ ∃ J ∈ G, productBox L ⊆ productBox J},
        rawProductDifference L.1 F.1 := by
  rw [(grid_removedDifference_hasSum hd D n I N hI G hG F hf hs).2.tsum_eq,
    sub_sub_cancel]

/-- Every removed grid rectangle is annihilated, including those
strictly finer than the finite cutoff and the cutoff cubes themselves. -/
theorem grid_projection_annihilates
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (hI : ∀ j, I j ∈ (D j).cubes (n j))
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (L : ∀ i, Box (Fin (d i))) (hL : L ∈ gridRectangles D)
    (hremoved : ∃ J ∈ G, productBox L ⊆ productBox J) :
    rawProductDifference L (finiteProjectionMap I N G F).1 = 0 := by
  rcases grid_removed_cases hd D n I N hI G hG L hL hremoved with hmem | hcut
  · rw [rawProductDifference_eq_productDifferenceMap L (finiteProjectionMap I N G F)]
    have ht := congrArg (fun T : Module.End ℝ (boundedMeasurableFunctions d) => (T F).1)
      (productDifferenceMap_mul_finiteProjectionMap I N hd G L hmem)
    simpa only [Module.End.mul_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero] using ht
  · obtain ⟨i, a, hLi, hLI, hcut⟩ := hcut
    have hclosure := finiteProjectionMap_productStep_closure I N G F hf hs
    exact rawProductDifference_eq_zero_of_cutoff D n I N hI
      (finiteProjectionMap I N G F) hclosure.1 hclosure.2 L i a hLi hLI hcut

end ReyZygmund.Projection
