import ReyZygmund.MathlibOnly.Proof.EstimateDefinitions
import ReyZygmund.Projection.LocalProductExpansion

/-!
# The finite proof under weak incomparability

The proof uses the enlarged family `G ∪ averagingRectangles I N G`
throughout its representation and maximal estimates. Weak incomparability
prohibits strict containment in every coordinate factor.

The enlargement removes exactly the original difference indices, so its common
projection is unchanged. Its weak incomparability follows from the finite dyadic
geometry. The formula in fewer coordinates holds for every family. Applying it
and preserved averages to the enlarged family gives the signed representation.
The subsequent analytic argument is in `Maximal.WeaklyIncomparableFinite`.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection
open MathlibOnly.Proof.Estimates (WeaklyIncomparable)

variable {m : ℕ} {d : Fin m → ℕ}

/-- Each removed full difference has zero
average on an original rectangle under weak incomparability. -/
theorem Projection.weaklyIncomparable_preserves_averages
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : WeaklyIncomparable (G : Set (∀ i, Box (Fin (d i)))))
    (R : ∀ i, Box (Fin (d i))) (hR : R ∈ G) :
    productAverageMap Finset.univ R * finiteProjectionMap I N G =
      productAverageMap Finset.univ R := by
  exact original_averages_preserved_of_weaker_containment I N hd G hG hweak R hR

/-- The full average of the projected
function is a signed sum of its averages in fewer coordinates. The family is
arbitrary; weak incomparability and preservation of the input average play no role. -/
theorem Projection.finite_lower_coordinate_averages
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (R : ∀ i, Box (Fin (d i))) (hR : R ∈ G)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (x : ProductPoint d) (hx : x ∈ productBox R) :
    (productAverageMap Finset.univ R (finiteProjectionMap I N G F)).1 x =
      ∑ A ∈ ((Finset.univ : Finset (Fin m)).powerset.erase Finset.univ),
        (-1 : ℝ) ^ (m + 1 + A.card) *
          (productAverageMap A R (finiteProjectionMap I N G F)).1 x := by
  let FP := finiteProjectionMap I N G F
  have hc := finiteProjectionMap_productStep_closure I N G F hf hs
  have hzero :
      (∑ L ∈ (productInterior I N).filter (fun L => ∀ i, L i ≤ R i),
        (productDifferenceMap Finset.univ L FP).1 x) = 0 := by
    apply Finset.sum_eq_zero
    intro L hL
    obtain ⟨hLi, hLR⟩ := Finset.mem_filter.mp hL
    have hremoved : L ∈ removedIndices I N G :=
      Finset.mem_filter.mpr ⟨hLi, R, hR, hLR⟩
    have h := congrArg
      (fun T : Module.End ℝ (boundedMeasurableFunctions d) => (T F).1 x)
      (productDifferenceMap_mul_finiteProjectionMap I N hd G L hremoved)
    simpa [FP, Module.End.mul_apply] using h
  have hexp := local_product_expansion I N hd R (mem_productDescendants.mp (hG hR))
    FP hc.1 hc.2 x hx
  have hfull :
      (∑ A ∈ (Finset.univ : Finset (Fin m)).powerset,
        (-1 : ℝ) ^ A.card * (productAverageMap A R FP).1 x) = 0 :=
    hexp.symm.trans hzero
  let S := ∑ A ∈ ((Finset.univ : Finset (Fin m)).powerset.erase Finset.univ),
    (-1 : ℝ) ^ A.card * (productAverageMap A R FP).1 x
  have hsplit : (-1 : ℝ) ^ m * (productAverageMap Finset.univ R FP).1 x + S = 0 := by
    have h := (Finset.add_sum_erase (Finset.univ : Finset (Fin m)).powerset
      (fun A => (-1 : ℝ) ^ A.card * (productAverageMap A R FP).1 x)
      (by simp : (Finset.univ : Finset (Fin m)) ∈ Finset.univ.powerset)).trans hfull
    simpa only [Finset.card_univ, Fintype.card_fin, S] using h
  have hval : (-1 : ℝ) ^ m * (productAverageMap Finset.univ R FP).1 x = -S := by
    linarith
  have hsign : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) *
        (productAverageMap Finset.univ R FP).1 x := by rw [hsign, one_mul]
    _ = (-1 : ℝ) ^ m *
        ((-1 : ℝ) ^ m * (productAverageMap Finset.univ R FP).1 x) := by ring
    _ = -((-1 : ℝ) ^ m) * S := by rw [hval]; ring
    _ = ∑ A ∈ ((Finset.univ : Finset (Fin m)).powerset.erase Finset.univ),
        -((-1 : ℝ) ^ m) *
          ((-1 : ℝ) ^ A.card * (productAverageMap A R FP).1 x) := by
      exact Finset.mul_sum _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro A _
      simp only [pow_add, pow_one]
      ring

/-- A descendant strictly containing another descendant is above the cutoff.
This also covers zero cutoff depth: then the strict containment is impossible. -/
private theorem interior_of_descendant_lt {ι : Type*} [Fintype ι]
    {I R S : Box ι} {N : ℕ}
    (hR : R ∈ descendants I N) (hS : S ∈ descendants I N) (hRS : R < S) :
    S ∈ interior I N := by
  obtain ⟨k, hk, hSk⟩ := mem_descendants.mp hS
  refine mem_interior.mpr ⟨k, lt_of_le_of_ne hk ?_, hSk⟩
  intro hkN
  subst k
  obtain ⟨j, hj, hRj⟩ := mem_descendants.mp hR
  obtain ⟨P, hP, hSP⟩ := level_refines I hj hSk
  have hRP : R = P :=
    (level I j).eq_of_le_of_le hRj hP le_rfl (hRS.le.trans hSP)
  exact (not_lt_of_ge (hSP.trans hRP.symm.le)) hRS

/-- Adding the averaging rectangles
does not add any interior difference index. No weak incomparability is needed. -/
theorem Projection.removedIndices_union_averagingRectangles
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) :
    removedIndices I N (G ∪ averagingRectangles I N G) = removedIndices I N G := by
  ext L
  constructor
  · intro hL
    obtain ⟨hLi, R, hR, hLR⟩ := Finset.mem_filter.mp hL
    rcases Finset.mem_union.mp hR with hR | hR
    · exact Finset.mem_filter.mpr ⟨hLi, R, hR, hLR⟩
    · exact interior_below_averagingRectangle_removed I N hd G R hR L hLi hLR
  · intro hL
    obtain ⟨hLi, R, hR, hLR⟩ := Finset.mem_filter.mp hL
    exact Finset.mem_filter.mpr ⟨hLi, R, Finset.mem_union_left _ hR, hLR⟩

/-- The enlarged family has the same projection as the original family. -/
theorem Projection.finiteProjectionMap_union_averagingRectangles
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) :
    finiteProjectionMap I N (G ∪ averagingRectangles I N G) =
      finiteProjectionMap I N G := by
  unfold finiteProjectionMap
  rw [removedIndices_union_averagingRectangles I N hd G]

/-- An averaging rectangle
whose factors are all above the cutoff lies below an original rectangle. -/
theorem Projection.averagingRectangle_interior_below_original
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (R : ∀ i, Box (Fin (d i)))
    (hR : R ∈ averagingRectangles I N G) (hRi : R ∈ productInterior I N) :
    ∃ J ∈ G, ∀ i, R i ≤ J i := by
  obtain ⟨_, J, hJ, hRJ⟩ := Finset.mem_filter.mp
    (interior_below_averagingRectangle_removed I N hd G R hR R hRi (fun _ => le_rfl))
  exact ⟨J, hJ, hRJ⟩

/-- Containment of an averaging rectangle
in an original rectangle leaves one whole factor unchanged. -/
theorem Projection.averagingRectangle_equal_factor_of_le
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (R : ∀ i, Box (Fin (d i)))
    (hR : R ∈ averagingRectangles I N G) (J : ∀ i, Box (Fin (d i)))
    (hJ : J ∈ G) (hRJ : ∀ i, R i ≤ J i) :
    ∃ i, R i = J i := by
  obtain ⟨_, j, hRj⟩ := mem_averagingRectangles.mp hR
  have hJe : J j ∈ eligibleProjections j G R := by
    exact Finset.mem_image.mpr
      ⟨J, Finset.mem_filter.mpr ⟨hJ, fun i _ => hRJ i⟩, rfl⟩
  have hJR : J j ≤ R j :=
    (mem_maximalCubes.mp hRj).2 (J j) (Finset.mem_union_left _ hJe) (hRJ j)
  exact ⟨j, le_antisymm (hRJ j) hJR⟩

/-- The union of the original and averaging families is weakly incomparable;
no inclusion of the original family in the averaging family is needed. -/
theorem Projection.weaklyIncomparable_union_averagingRectangles
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : WeaklyIncomparable (G : Set (∀ i, Box (Fin (d i))))) :
    WeaklyIncomparable
      ((G ∪ averagingRectangles I N G : Finset (∀ i, Box (Fin (d i)))) :
        Set (∀ i, Box (Fin (d i)))) := by
  have hfamily : G ∪ averagingRectangles I N G ⊆ productDescendants I N := by
    intro R hR
    rcases Finset.mem_union.mp hR with hR | hR
    · exact hG hR
    · exact averagingRectangles_subset_productDescendants I N G hR
  intro R hR S hS hRS
  have hSi : S ∈ productInterior I N := by
    apply mem_productInterior.mpr
    intro i
    exact interior_of_descendant_lt
      (mem_productDescendants.mp (hfamily hR) i)
      (mem_productDescendants.mp (hfamily hS) i) (hRS i)
  have hSJ : ∃ J ∈ G, ∀ i, S i ≤ J i := by
    rcases Finset.mem_union.mp hS with hS | hS
    · exact ⟨S, hS, fun _ => le_rfl⟩
    · exact averagingRectangle_interior_below_original I N hd G S hS hSi
  obtain ⟨J, hJ, hSJ⟩ := hSJ
  have hRJ : ∀ i, R i < J i := fun i => lt_of_lt_of_le (hRS i) (hSJ i)
  rcases Finset.mem_union.mp hR with hR | hR
  · exact hweak R hR J hJ hRJ
  · obtain ⟨i, hi⟩ :=
      averagingRectangle_equal_factor_of_le I N G R hR J hJ (fun i => (hRJ i).le)
    exact (ne_of_lt (hRJ i)) hi

/-- On the enlarged family, the unchanged
projection preserves every original or averaging rectangle average. -/
theorem Projection.weaklyIncomparable_union_preserves_averages
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : WeaklyIncomparable (G : Set (∀ i, Box (Fin (d i)))))
    (R : ∀ i, Box (Fin (d i))) (hR : R ∈ G ∪ averagingRectangles I N G) :
    productAverageMap Finset.univ R * finiteProjectionMap I N G =
      productAverageMap Finset.univ R := by
  have hfamily : G ∪ averagingRectangles I N G ⊆ productDescendants I N := by
    intro S hS
    rcases Finset.mem_union.mp hS with hS | hS
    · exact hG hS
    · exact averagingRectangles_subset_productDescendants I N G hS
  have hpres := weaklyIncomparable_preserves_averages I N hd
    (G ∪ averagingRectangles I N G) hfamily
    (weaklyIncomparable_union_averagingRectangles I N hd G hG hweak) R hR
  simpa only [finiteProjectionMap_union_averagingRectangles I N hd G] using hpres

/-- The signed formula on the enlarged family
uses the projection of the original weakly incomparable family. -/
theorem Projection.finite_weakly_incomparable_representation
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : WeaklyIncomparable (G : Set (∀ i, Box (Fin (d i)))))
    (R : ∀ i, Box (Fin (d i))) (hR : R ∈ G ∪ averagingRectangles I N G)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (x : ProductPoint d) (hx : x ∈ productBox R) :
    (productAverageMap Finset.univ R F).1 x =
      ∑ A ∈ ((Finset.univ : Finset (Fin m)).powerset.erase Finset.univ),
        (-1 : ℝ) ^ (m + 1 + A.card) *
          (productAverageMap A R (finiteProjectionMap I N G F)).1 x := by
  have hfamily : G ∪ averagingRectangles I N G ⊆ productDescendants I N := by
    intro S hS
    rcases Finset.mem_union.mp hS with hS | hS
    · exact hG hS
    · exact averagingRectangles_subset_productDescendants I N G hS
  have hlow := finite_lower_coordinate_averages I N hd
    (G ∪ averagingRectangles I N G) hfamily R hR F hf hs x hx
  rw [finiteProjectionMap_union_averagingRectangles I N hd G] at hlow
  have hpres :
      (productAverageMap Finset.univ R (finiteProjectionMap I N G F)).1 x =
        (productAverageMap Finset.univ R F).1 x := by
    have h := congrArg
      (fun T : Module.End ℝ (boundedMeasurableFunctions d) => (T F).1 x)
      (weaklyIncomparable_union_preserves_averages I N hd G hG hweak R hR)
    simpa only [Module.End.mul_apply] using h
  exact hpres.symm.trans hlow

end ReyZygmund
