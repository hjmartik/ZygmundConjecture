import ReyZygmund.Sharpness.CoordinateRetention
import ReyZygmund.Sharpness.SpatialPartitions
import ReyZygmund.Geometry.ProductContainment
import ReyZygmund.Continuous.DyadicExtension

/-! # Rectangle families at fixed scale indices

The retained coordinate families from `exists_coordinate_retention` determine
dyadic refinements for each scale index. Their finite product gives a rectangle
family. Taking the union over indices gives the total family, counting each
rectangle once.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Sharpness

open Geometry

variable {n N : ℕ} {d : Fin (n + 3) → ℕ}

private noncomputable def spatialCoordinates (s : ℕ)
    (Q : ∀ j, Box (Fin (d j)))
    (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ))))
    (a : Fin (n + 2) → Fin N) : ∀ j, Finset (Box (Fin (d j))) :=
  Fin.cons (level (Q 0) (sharpGeneration s a 0).toNat).boxes
    (fun i => (P i (a i).val).biUnion (fun R =>
      (level R (sharpGeneration s a i.succ -
        (s : ℤ) * selectionScale N i (a i).val).toNat).boxes))

/-- The paper's family at the fixed scale index `a`. -/
noncomputable def sharpSpatialFamily (s : ℕ) (Q : ∀ j, Box (Fin (d j)))
    (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ))))
    (a : Fin (n + 2) → Fin N) : Finset (∀ j, Box (Fin (d j))) :=
  Fintype.piFinset (spatialCoordinates s Q P a)

/-- The finite union over all prescribed scale indices. -/
noncomputable def sharpSpatialTotal (N s : ℕ) (Q : ∀ j, Box (Fin (d j)))
    (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ)))) :
    Finset (∀ j, Box (Fin (d j))) :=
  Finset.univ.biUnion (fun a : Fin (n + 2) → Fin N => sharpSpatialFamily s Q P a)

private theorem spatialCoordinates_properties (hN : 2 ≤ N) (s : ℕ)
    (D : ∀ j, DyadicGrid (d j)) (Q : ∀ j, Box (Fin (d j)))
    (hQ : ∀ j, Q j ∈ (D j).cubes 0)
    (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ))))
    (hP : ∀ i k R, R ∈ P i k →
      R ∈ (D i.succ).cubes ((s : ℤ) * selectionScale N i k))
    (a : Fin (n + 2) → Fin N) :
    (∀ j R, R ∈ spatialCoordinates s Q P a j →
      R ∈ (D j).cubes (sharpGeneration s a j)) ∧
      boxUnion (spatialCoordinates s Q P a 0) = (Q 0 : Set (Fin (d 0) → ℝ)) ∧
      ∀ i, boxUnion (spatialCoordinates s Q P a i.succ) = boxUnion (P i (a i).val) := by
  have href (i : Fin (n + 2)) :=
    refine_grid_partition (D i.succ) ((s : ℤ) * selectionScale N i (a i).val)
      (sharpGeneration s a i.succ) (sharpGeneration_selection_scaled s a i).1
      (P i (a i).val) (hP i (a i).val)
  refine ⟨?_, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · intro R hR
      have hcast : ((sharpGeneration s a 0).toNat : ℤ) = sharpGeneration s a 0 := by
        have h := sharpGeneration_nonneg hN s a 0
        omega
      change R ∈ level (Q 0) (sharpGeneration s a 0).toNat at hR
      simpa only [zero_add, hcast] using (D 0).mem_cubes_of_mem_level (hQ 0) hR
    · intro R hR
      exact (href i).1 R hR
  · change (level (Q 0) (sharpGeneration s a 0).toNat).iUnion = _
    exact (level_isPartition (Q 0) _).iUnion_eq
  · intro i
    exact (href i).2.1

/-- The fixed-index family partitions the prescribed retained product
set, with exact generations and a pointwise real indicator identity. -/
theorem sharpSpatialFamily_partition (hN : 2 ≤ N) (s : ℕ)
    (D : ∀ j, DyadicGrid (d j)) (Q : ∀ j, Box (Fin (d j)))
    (hQ : ∀ j, Q j ∈ (D j).cubes 0)
    (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ))))
    (hP : ∀ i k R, R ∈ P i k →
      R ∈ (D i.succ).cubes ((s : ℤ) * selectionScale N i k))
    (a : Fin (n + 2) → Fin N) :
    (∀ R ∈ sharpSpatialFamily s Q P a, ∀ j,
      R j ∈ (D j).cubes (sharpGeneration s a j)) ∧
      (⋃ R ∈ sharpSpatialFamily s Q P a, productBox R) =
        {x : ProductPoint d | x 0 ∈ Q 0 ∧
          ∀ i, x i.succ ∈ boxUnion (P i (a i).val)} ∧
      Set.PairwiseDisjoint
        (↑(sharpSpatialFamily s Q P a) : Set (∀ j, Box (Fin (d j)))) productBox ∧
      ∀ x : ProductPoint d,
        (∑ R ∈ sharpSpatialFamily s Q P a,
          (productBox R).indicator (fun _ => (1 : ℝ)) x) =
          (Q 0 : Set (Fin (d 0) → ℝ)).indicator (fun _ => (1 : ℝ)) (x 0) *
            ∏ i, (boxUnion (P i (a i).val)).indicator (fun _ => (1 : ℝ)) (x i.succ) := by
  obtain ⟨hgen, hzero, hsucc⟩ := spatialCoordinates_properties hN s D Q hQ P hP a
  obtain ⟨hcover, hdis, hind⟩ := product_grid_partition D (sharpGeneration s a)
    (spatialCoordinates s Q P a) hgen
  have hset : Set.pi Set.univ (fun j => boxUnion (spatialCoordinates s Q P a j)) =
      {x : ProductPoint d | x 0 ∈ Q 0 ∧
        ∀ i, x i.succ ∈ boxUnion (P i (a i).val)} := by
    ext x
    constructor
    · intro hx
      have h := Set.mem_univ_pi.mp hx
      exact ⟨by simpa only [hzero, Box.mem_coe] using h 0,
        fun i => by simpa only [hsucc i] using h i.succ⟩
    · intro hx
      apply Set.mem_univ_pi.mpr
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · rw [hzero]
        exact hx.1
      · rw [hsucc i]
        exact hx.2 i
  refine ⟨?_, hcover.trans hset, hdis, ?_⟩
  · intro R hR j
    exact hgen j (R j) (Fintype.mem_piFinset.mp hR j)
  · intro x
    change (∑ R ∈ Fintype.piFinset (spatialCoordinates s Q P a),
      (productBox R).indicator (fun _ => (1 : ℝ)) x) = _
    rw [hind x, Fin.prod_univ_succ, hzero]
    congr 1
    exact Finset.prod_congr rfl (fun i _ => by rw [hsucc i])

/-- No eligible rectangle is omitted: generation and containment in
the retained product set characterize membership in the constructed family. -/
theorem mem_sharpSpatialFamily_iff (hN : 2 ≤ N) (s : ℕ)
    (D : ∀ j, DyadicGrid (d j)) (Q : ∀ j, Box (Fin (d j)))
    (hQ : ∀ j, Q j ∈ (D j).cubes 0)
    (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ))))
    (hP : ∀ i k R, R ∈ P i k →
      R ∈ (D i.succ).cubes ((s : ℤ) * selectionScale N i k))
    (a : Fin (n + 2) → Fin N) (R : ∀ j, Box (Fin (d j))) :
    R ∈ sharpSpatialFamily s Q P a ↔
      (∀ j, R j ∈ (D j).cubes (sharpGeneration s a j)) ∧
      productBox R ⊆ {x : ProductPoint d | x 0 ∈ Q 0 ∧
        ∀ i, x i.succ ∈ boxUnion (P i (a i).val)} := by
  have hp := sharpSpatialFamily_partition hN s D Q hQ P hP a
  constructor
  · intro hR
    refine ⟨hp.1 R hR, ?_⟩
    intro x hx
    rw [← hp.2.1]
    exact Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨hR, hx⟩⟩
  · rintro ⟨hgen, hsub⟩
    have hx : (fun j => (R j).upper) ∈ productBox R :=
      (mem_productBox R _).mpr (fun j => (R j).upper_mem)
    have hxcover := hsub hx
    rw [← hp.2.1] at hxcover
    obtain ⟨S, hxS⟩ := Set.mem_iUnion.mp hxcover
    obtain ⟨hS, hxS⟩ := Set.mem_iUnion.mp hxS
    have hRS : R = S := by
      funext j
      exact (D j).eq_of_mem_of_mem (hgen j) (hp.1 S hS j)
        (R j).upper_mem ((mem_productBox S _).mp hxS j)
    exact hRS.symm ▸ hS

private theorem generation_le_of_le {e : ℕ} (he : 0 < e)
    (D : DyadicGrid e) {g h : ℤ} {R S : Box (Fin e)}
    (hR : R ∈ D.cubes g) (hS : S ∈ D.cubes h) (hRS : R ≤ S) : h ≤ g := by
  let i : Fin e := ⟨0, he⟩
  have hb := Box.le_iff_bounds.mp hRS
  have hw : R.upper i - R.lower i ≤ S.upper i - S.lower i :=
    sub_le_sub (hb.2 i) (hb.1 i)
  rw [D.width g R hR i, D.width h S hS i] at hw
  have hneg := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hw
  omega

private theorem spatial_index_eq_of_subset (hN : 2 ≤ N) (s : ℕ) (hs : 1 ≤ s)
    (hd : ∀ j, 0 < d j) (D : ∀ j, DyadicGrid (d j))
    (Q : ∀ j, Box (Fin (d j))) (hQ : ∀ j, Q j ∈ (D j).cubes 0)
    (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ))))
    (hP : ∀ i k R, R ∈ P i k →
      R ∈ (D i.succ).cubes ((s : ℤ) * selectionScale N i k))
    {a b : Fin (n + 2) → Fin N} {R S : ∀ j, Box (Fin (d j))}
    (hR : R ∈ sharpSpatialFamily s Q P a) (hS : S ∈ sharpSpatialFamily s Q P b)
    (hRS : productBox R ⊆ productBox S) : a = b := by
  have hgenR := (sharpSpatialFamily_partition hN s D Q hQ P hP a).1 R hR
  have hgenS := (sharpSpatialFamily_partition hN s D Q hQ P hP b).1 S hS
  exact sharpGeneration_eq_of_ge hN hs a b (fun j =>
    generation_le_of_le (hd j) (D j) (hgenR j) (hgenS j)
      ((productBox_subset_iff R S).mp hRS j))

/-- The total family has the paper's classical scale relation, is
incomparable, has precisely the top rectangle as its shadow, and assigns every
rectangle to a unique index. The hypotheses on `P` are properties
proved by the concrete coordinate-retention construction. -/
theorem sharpSpatialTotal_properties (hN : 2 ≤ N) (s : ℕ) (hs : 1 ≤ s)
    (hd : ∀ j, 0 < d j) (D : ∀ j, DyadicGrid (d j))
    (Q : ∀ j, Box (Fin (d j))) (hQ : ∀ j, Q j ∈ (D j).cubes 0)
    (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ))))
    (hP : ∀ i k R, R ∈ P i k →
      R ∈ (D i.succ).cubes ((s : ℤ) * selectionScale N i k))
    (hPzero : ∀ i, boxUnion (P i 0) = (Q i.succ : Set (Fin (d i.succ) → ℝ)))
    (hPnest : ∀ i k, boxUnion (P i (k + 1)) ⊆ boxUnion (P i k)) :
    (↑(sharpSpatialTotal N s Q P) : Set (∀ j, Box (Fin (d j)))) ⊆
        Continuous.dyadicPhiRectangles D (fun k : Fin (n + 2) → ℤ => ∑ i, k i) ∧
      (∀ R ∈ sharpSpatialTotal N s Q P, ∀ S ∈ sharpSpatialTotal N s Q P,
        productBox R ⊆ productBox S → R = S) ∧
      (⋃ R ∈ sharpSpatialTotal N s Q P, productBox R) = productBox Q ∧
      ∀ R ∈ sharpSpatialTotal N s Q P,
        ∃! a : Fin (n + 2) → Fin N, R ∈ sharpSpatialFamily s Q P a := by
  have hmem (R : ∀ j, Box (Fin (d j))) :
      R ∈ sharpSpatialTotal N s Q P ↔
        ∃ a : Fin (n + 2) → Fin N, R ∈ sharpSpatialFamily s Q P a := by
    simp only [sharpSpatialTotal, Finset.mem_biUnion, Finset.mem_univ, true_and]
  have hroot (i : Fin (n + 2)) (k : ℕ) :
      boxUnion (P i k) ⊆ (Q i.succ : Set (Fin (d i.succ) → ℝ)) := by
    induction k with
    | zero => exact (hPzero i).subset
    | succ k ih => exact (hPnest i k).trans ih
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R hR
    obtain ⟨a, ha⟩ := (hmem R).mp hR
    have hgen := (sharpSpatialFamily_partition hN s D Q hQ P hP a).1 R ha
    refine ⟨(fun i => -sharpGeneration s a i.castSucc), ?_⟩
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [Fin.snoc_last, Finset.sum_neg_distrib, neg_neg,
        ← sharpGeneration_sum s a] using hgen (Fin.last (n + 2))
    · simpa only [Fin.snoc_castSucc, neg_neg] using hgen i.castSucc
  · intro R hR S hS hRS
    obtain ⟨a, ha⟩ := (hmem R).mp hR
    obtain ⟨b, hb⟩ := (hmem S).mp hS
    have hab := spatial_index_eq_of_subset hN s hs hd D Q hQ P hP ha hb hRS
    subst b
    have hgen := (sharpSpatialFamily_partition hN s D Q hQ P hP a).1
    funext j
    exact (D j).eq_of_mem_of_mem (hgen R ha j) (hgen S hb j) (R j).upper_mem
      (((productBox_subset_iff R S).mp hRS j) (R j).upper_mem)
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨R, hxR⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hR, hxR⟩ := Set.mem_iUnion.mp hxR
      obtain ⟨a, ha⟩ := (hmem R).mp hR
      have hxset := ((mem_sharpSpatialFamily_iff hN s D Q hQ P hP a R).mp ha).2 hxR
      apply (mem_productBox Q x).mpr
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact hxset.1
      · simpa only [Box.mem_coe] using hroot i (a i).val (hxset.2 i)
    · intro x hx
      let a0 : Fin (n + 2) → Fin N := fun _ => ⟨0, by omega⟩
      have hxset : x ∈ {y : ProductPoint d | y 0 ∈ Q 0 ∧
          ∀ i, y i.succ ∈ boxUnion (P i (a0 i).val)} := by
        refine ⟨(mem_productBox Q x).mp hx 0, ?_⟩
        intro i
        change x i.succ ∈ boxUnion (P i 0)
        rw [hPzero i]
        simpa only [Box.mem_coe] using (mem_productBox Q x).mp hx i.succ
      rw [← (sharpSpatialFamily_partition hN s D Q hQ P hP a0).2.1] at hxset
      obtain ⟨R, hxR⟩ := Set.mem_iUnion.mp hxset
      obtain ⟨hR, hxR⟩ := Set.mem_iUnion.mp hxR
      exact Set.mem_iUnion.mpr ⟨R,
        Set.mem_iUnion.mpr ⟨(hmem R).mpr ⟨a0, hR⟩, hxR⟩⟩
  · intro R hR
    obtain ⟨a, ha⟩ := (hmem R).mp hR
    refine ⟨a, ha, ?_⟩
    intro b hb
    exact spatial_index_eq_of_subset hN s hs hd D Q hQ P hP hb ha subset_rfl

end ReyZygmund.Sharpness
