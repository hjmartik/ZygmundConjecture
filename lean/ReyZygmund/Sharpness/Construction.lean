import ReyZygmund.Sharpness.SpatialWitnesses

/-! # Finite rectangle families for sharpness

Construct retained cube families in each coordinate. Their products and the
associated disjoint subsets give incomparability and sparseness. We also compute
the set of maximum overlap and its volume. Subsequent modules normalize the top
cubes, pass to Euclidean coordinates, and prove divergence of the exponential
integrals. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Sharpness

open Geometry

private theorem construction_volume_pi_real {m : ℕ} {d : Fin m → ℕ}
    (U : ∀ i, Set (Fin (d i) → ℝ)) :
    volume.real (Set.pi Set.univ U) = ∏ i, volume.real (U i) := by
  change (Measure.pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
    (Set.pi Set.univ U)).toReal = ∏ i, (volume (U i)).toReal
  rw [Measure.pi_pi, ENNReal.toReal_prod]

/-- The concrete finite Section 7 construction, with no conditional retained
families or sparse/overlap conclusions among the assumptions. -/
theorem exists_sharp_spatial_construction (n N s : ℕ) (hN : 2 ≤ N) (hs : 1 ≤ s)
    (d : Fin (n + 3) → ℕ) (hd : ∀ j, 0 < d j)
    (D : ∀ j, DyadicGrid (d j)) (Q : ∀ j, Box (Fin (d j)))
    (hQ : ∀ j, Q j ∈ (D j).cubes 0) :
    ∃ G : Finset (∀ j, Box (Fin (d j))),
      ∃ E : (∀ j, Box (Fin (d j))) → Set (ProductPoint d),
        ∃ L : Set (ProductPoint d),
      (↑G : Set (∀ j, Box (Fin (d j)))) ⊆
        Continuous.dyadicPhiRectangles D (fun k : Fin (n + 2) → ℤ => ∑ i, k i) ∧
      (∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → R = S) ∧
      (⋃ R ∈ G, productBox R) = productBox Q ∧
      (∀ R ∈ G, MeasurableSet (E R) ∧ E R ⊆ productBox R ∧
        volume.real (E R) = (1 - (2 : ℝ) ^ (-(s : ℤ))) ^ (n + 2) *
          volume.real (productBox R)) ∧
      Set.PairwiseDisjoint (↑G : Set (∀ j, Box (Fin (d j)))) E ∧
      MeasurableSet L ∧ L ⊆ (⋃ R ∈ G, productBox R) ∧
      L = {x : ProductPoint d | (∑ R ∈ G,
        (productBox R).indicator (fun _ => (1 : ℝ)) x) = (N : ℝ) ^ (n + 2)} ∧
      volume.real L = ((2 : ℝ) ^ (-(s : ℤ))) ^ ((n + 2) * (N - 1)) *
        volume.real (productBox Q) := by
  obtain ⟨P, _, hzero, hgen, _, hnest, hmeas, hmass, hlocal⟩ :=
    exists_coordinate_retention n N s hN (fun i => d i.succ) (fun i => hd i.succ)
      (fun i => D i.succ) (fun i => Q i.succ) (fun i => hQ i.succ)
  have hG := sharpSpatialTotal_properties hN s hs hd D Q hQ P hgen hzero hnest
  obtain ⟨E, _, hE, hEdis⟩ :=
    sharpSpatialTotal_witnesses hN s hs hd D Q hQ P hgen hzero hnest hlocal
  let L : Set (ProductPoint d) := Set.pi Set.univ
    (Fin.cons (Q 0 : Set (Fin (d 0) → ℝ)) (fun i => boxUnion (P i (N - 1))))
  have hLset : L = {x : ProductPoint d | x 0 ∈ Q 0 ∧
      ∀ i, x i.succ ∈ boxUnion (P i (N - 1))} := by
    ext x
    constructor
    · intro hx
      have hi := Set.mem_univ_pi.mp hx
      exact ⟨by simpa only [Fin.cons_zero, Box.mem_coe] using hi 0,
        fun i => by simpa only [Fin.cons_succ] using hi i.succ⟩
    · intro hx
      apply Set.mem_univ_pi.mpr
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simpa only [Fin.cons_zero, Box.mem_coe] using hx.1
      · simpa only [Fin.cons_succ] using hx.2 i
  have hLm : MeasurableSet L := by
    apply MeasurableSet.univ_pi
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact (Q 0).measurableSet_coe
    · exact (hmeas i (N - 1)).1
  have hroot (i : Fin (n + 2)) (k : ℕ) :
      boxUnion (P i k) ⊆ (Q i.succ : Set (Fin (d i.succ) → ℝ)) := by
    induction k with
    | zero => exact (hzero i).subset
    | succ k ih => exact (hnest i k).trans ih
  refine ⟨sharpSpatialTotal N s Q P, E, L, hG.1, hG.2.1, hG.2.2.1,
    hE, hEdis, hLm, ?_, ?_, ?_⟩
  · rw [hG.2.2.1]
    intro x hx
    rw [hLset] at hx
    apply (mem_productBox Q x).mpr
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact hx.1
    · simpa only [Box.mem_coe] using hroot i (N - 1) (hx.2 i)
  · exact hLset.trans (sharpSpatialTotal_maximum_set hN s hs hd D Q hQ P
      hgen hzero hnest).symm
  · have hvolL : volume.real L = volume.real (Q 0 : Set (Fin (d 0) → ℝ)) *
        ∏ i : Fin (n + 2), volume.real (boxUnion (P i (N - 1))) := by
      simp only [L, construction_volume_pi_real, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ]
    have hvolQ : volume.real (productBox Q) =
        volume.real (Q 0 : Set (Fin (d 0) → ℝ)) *
          ∏ i : Fin (n + 2), volume.real (Q i.succ : Set (Fin (d i.succ) → ℝ)) := by
      rw [productBox, construction_volume_pi_real, Fin.prod_univ_succ]
    rw [hvolL, hvolQ]
    simp_rw [hmass]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul, Nat.mul_comm (N - 1) (n + 2)]
    ring

end ReyZygmund.Sharpness
