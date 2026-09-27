import ReyZygmund.Sharpness.SpatialFamily
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Disjoint subsets establishing sparseness

For each rectangle, take its first cube factor and, in each remaining coordinate,
remove the next retained set from that rectangle's cube factor. Their product is
its sparse subset. The local measure identities give its required measure.
The set identities hold pointwise.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Sharpness

open Geometry

variable {n N : ℕ} {d : Fin (n + 3) → ℕ}

/-- The set `E_I` in the sharpness construction, for a rectangle at index `a`. -/
def sharpSpatialWitness
    (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ))))
    (a : Fin (n + 2) → Fin N) (R : ∀ j, Box (Fin (d j))) : Set (ProductPoint d) :=
  Set.pi Set.univ (Fin.cons (R 0 : Set (Fin (d 0) → ℝ))
    (fun i => (R i.succ : Set (Fin (d i.succ) → ℝ)) \
      boxUnion (P i ((a i).val + 1))))

private theorem mem_spatialWitness
    (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ))))
    (a : Fin (n + 2) → Fin N) (R : ∀ j, Box (Fin (d j))) (x : ProductPoint d) :
    x ∈ sharpSpatialWitness P a R ↔ x 0 ∈ R 0 ∧
      ∀ i, x i.succ ∈ R i.succ ∧ x i.succ ∉ boxUnion (P i ((a i).val + 1)) := by
  constructor
  · intro hx
    have h := Set.mem_univ_pi.mp hx
    refine ⟨by simpa only [Fin.cons_zero, Box.mem_coe] using h 0, ?_⟩
    intro i
    have hi := h i.succ
    change x i.succ ∈ (R i.succ : Set (Fin (d i.succ) → ℝ)) \
      boxUnion (P i ((a i).val + 1)) at hi
    exact ⟨by simpa only [Box.mem_coe] using hi.1, hi.2⟩
  · intro hx
    apply Set.mem_univ_pi.mpr
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa only [Fin.cons_zero, Box.mem_coe] using hx.1
    · change x i.succ ∈ (R i.succ : Set (Fin (d i.succ) → ℝ)) \
        boxUnion (P i ((a i).val + 1))
      exact ⟨by simpa only [Box.mem_coe] using (hx.2 i).1, (hx.2 i).2⟩

private theorem spatialWitness_subset
    (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ))))
    (a : Fin (n + 2) → Fin N) (R : ∀ j, Box (Fin (d j))) :
    sharpSpatialWitness P a R ⊆ productBox R := by
  intro x hx
  have h := (mem_spatialWitness P a R x).mp hx
  apply (mem_productBox R x).mpr
  intro j
  exact Fin.cases h.1 (fun i => (h.2 i).1) j

private theorem measurableSet_spatialWitness
    (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ))))
    (a : Fin (n + 2) → Fin N) (R : ∀ j, Box (Fin (d j))) :
    MeasurableSet (sharpSpatialWitness P a R) := by
  apply MeasurableSet.univ_pi
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact (R 0).measurableSet_coe
  · exact (R i.succ).measurableSet_coe.diff (measurableSet_boxUnion _)

private theorem volume_pi_real {m : ℕ} {e : Fin m → ℕ}
    (U : ∀ i, Set (Fin (e i) → ℝ)) :
    volume.real (Set.pi Set.univ U) = ∏ i, volume.real (U i) := by
  change (Measure.pi (fun i => (volume : Measure (Fin (e i) → ℝ)))
    (Set.pi Set.univ U)).toReal = ∏ i, (volume (U i)).toReal
  rw [Measure.pi_pi, ENNReal.toReal_prod]

private theorem spatial_coordinate_subset (hN : 2 ≤ N) (s : ℕ)
    (D : ∀ j, DyadicGrid (d j)) (Q : ∀ j, Box (Fin (d j)))
    (hQ : ∀ j, Q j ∈ (D j).cubes 0)
    (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ))))
    (hP : ∀ i k R, R ∈ P i k →
      R ∈ (D i.succ).cubes ((s : ℤ) * selectionScale N i k))
    (a : Fin (n + 2) → Fin N) (R : ∀ j, Box (Fin (d j)))
    (hR : R ∈ sharpSpatialFamily s Q P a) (i : Fin (n + 2)) :
    (R i.succ : Set (Fin (d i.succ) → ℝ)) ⊆ boxUnion (P i (a i).val) := by
  intro y hy
  let x : ProductPoint d := Function.update (fun j => (R j).upper) i.succ y
  have hx : x ∈ productBox R := by
    apply (mem_productBox R x).mpr
    intro j
    by_cases hji : j = i.succ
    · subst j
      simpa only [x, Function.update_self, Box.mem_coe] using hy
    · simpa only [x, Function.update_of_ne hji] using (R j).upper_mem
  have hi := ((mem_sharpSpatialFamily_iff hN s D Q hQ P hP a R).mp hR).2 hx
  simpa only [x, Function.update_self] using hi.2 i

/-- The local retention identity gives the measure of `E_I` as the stated product
fraction of the rectangle's measure. -/
theorem sharpSpatialWitness_properties (hN : 2 ≤ N) (s : ℕ)
    (D : ∀ j, DyadicGrid (d j)) (Q : ∀ j, Box (Fin (d j)))
    (hQ : ∀ j, Q j ∈ (D j).cubes 0)
    (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ))))
    (hP : ∀ i k R, R ∈ P i k →
      R ∈ (D i.succ).cubes ((s : ℤ) * selectionScale N i k))
    (hlocal : ∀ (a : Fin (n + 2) → Fin N) i (I : Box (Fin (d i.succ))),
      I ∈ (D i.succ).cubes (sharpGeneration s a i.succ) →
      (I : Set (Fin (d i.succ) → ℝ)) ⊆ boxUnion (P i (a i).val) →
      volume.real ((I : Set (Fin (d i.succ) → ℝ)) ∩ boxUnion (P i ((a i).val + 1))) =
        (2 : ℝ) ^ (-(s : ℤ)) * volume.real (I : Set (Fin (d i.succ) → ℝ)))
    (a : Fin (n + 2) → Fin N) (R : ∀ j, Box (Fin (d j)))
    (hR : R ∈ sharpSpatialFamily s Q P a) :
    MeasurableSet (sharpSpatialWitness P a R) ∧
      sharpSpatialWitness P a R ⊆ productBox R ∧
      volume.real (sharpSpatialWitness P a R) =
        (1 - (2 : ℝ) ^ (-(s : ℤ))) ^ (n + 2) * volume.real (productBox R) := by
  refine ⟨measurableSet_spatialWitness P a R, spatialWitness_subset P a R, ?_⟩
  have hcoord (i : Fin (n + 2)) :
      volume.real ((R i.succ : Set (Fin (d i.succ) → ℝ)) \
          boxUnion (P i ((a i).val + 1))) =
        (1 - (2 : ℝ) ^ (-(s : ℤ))) *
          volume.real (R i.succ : Set (Fin (d i.succ) → ℝ)) := by
    have hl := hlocal a i (R i.succ)
      ((sharpSpatialFamily_partition hN s D Q hQ P hP a).1 R hR i.succ)
      (spatial_coordinate_subset hN s D Q hQ P hP a R hR i)
    have hsplit := measureReal_inter_add_sdiff (μ := volume)
      (s := (R i.succ : Set (Fin (d i.succ) → ℝ)))
      (measurableSet_boxUnion (P i ((a i).val + 1)))
      ((R i.succ).measure_coe_lt_top volume).ne
    rw [hl] at hsplit
    linarith
  have hw : volume.real (sharpSpatialWitness P a R) =
      volume.real (R 0 : Set (Fin (d 0) → ℝ)) *
        ∏ i, volume.real ((R i.succ : Set (Fin (d i.succ) → ℝ)) \
          boxUnion (P i ((a i).val + 1))) := by
    simp only [sharpSpatialWitness, volume_pi_real, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
  have hprod : volume.real (productBox R) =
      volume.real (R 0 : Set (Fin (d 0) → ℝ)) *
        ∏ i : Fin (n + 2), volume.real (R i.succ : Set (Fin (d i.succ) → ℝ)) := by
    rw [productBox, volume_pi_real, Fin.prod_univ_succ]
  rw [hw, hprod]
  simp_rw [hcoord]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

private theorem mem_spatialTotal_of_mem {s : ℕ}
    {Q : ∀ j, Box (Fin (d j))}
    {P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ)))}
    {a : Fin (n + 2) → Fin N} {R : ∀ j, Box (Fin (d j))}
    (hR : R ∈ sharpSpatialFamily s Q P a) : R ∈ sharpSpatialTotal N s Q P :=
  Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, hR⟩

private theorem spatialWitness_disjoint_of_ne (hN : 2 ≤ N) (s : ℕ)
    (D : ∀ j, DyadicGrid (d j)) (Q : ∀ j, Box (Fin (d j)))
    (hQ : ∀ j, Q j ∈ (D j).cubes 0)
    (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ))))
    (hP : ∀ i k R, R ∈ P i k →
      R ∈ (D i.succ).cubes ((s : ℤ) * selectionScale N i k))
    (hPnest : ∀ i k, boxUnion (P i (k + 1)) ⊆ boxUnion (P i k))
    {a b : Fin (n + 2) → Fin N} {R S : ∀ j, Box (Fin (d j))}
    (hR : R ∈ sharpSpatialFamily s Q P a) (hS : S ∈ sharpSpatialFamily s Q P b)
    (hab : a ≠ b) : Disjoint (sharpSpatialWitness P a R) (sharpSpatialWitness P b S) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
  have hmono : Antitone (fun k => boxUnion (P i k)) :=
    antitone_nat_of_succ_le (hPnest i)
  apply Set.disjoint_left.mpr
  intro x hxR hxS
  have hxR' := (mem_spatialWitness P a R x).mp hxR
  have hxS' := (mem_spatialWitness P b S x).mp hxS
  have hxA : x i.succ ∈ boxUnion (P i (a i).val) :=
    spatial_coordinate_subset hN s D Q hQ P hP a R hR i
      (by simpa only [Box.mem_coe] using (hxR'.2 i).1)
  have hxB : x i.succ ∈ boxUnion (P i (b i).val) :=
    spatial_coordinate_subset hN s D Q hQ P hP b S hS i
      (by simpa only [Box.mem_coe] using (hxS'.2 i).1)
  rcases lt_or_gt_of_ne hi with hlt | hlt
  · have hval : (a i).val + 1 ≤ (b i).val := by omega
    exact (hxR'.2 i).2 (hmono hval hxB)
  · have hval : (b i).val + 1 ≤ (a i).val := by omega
    exact (hxS'.2 i).2 (hmono hval hxA)

/-- Assign a disjoint subset to each rectangle of the total family, counting equal rectangles once.
The computed measure fraction gives sparseness for every parameter at most that fraction. -/
theorem sharpSpatialTotal_witnesses (hN : 2 ≤ N) (s : ℕ) (hs : 1 ≤ s)
    (hd : ∀ j, 0 < d j) (D : ∀ j, DyadicGrid (d j))
    (Q : ∀ j, Box (Fin (d j))) (hQ : ∀ j, Q j ∈ (D j).cubes 0)
    (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ))))
    (hP : ∀ i k R, R ∈ P i k →
      R ∈ (D i.succ).cubes ((s : ℤ) * selectionScale N i k))
    (hPzero : ∀ i, boxUnion (P i 0) = (Q i.succ : Set (Fin (d i.succ) → ℝ)))
    (hPnest : ∀ i k, boxUnion (P i (k + 1)) ⊆ boxUnion (P i k))
    (hlocal : ∀ (a : Fin (n + 2) → Fin N) i (I : Box (Fin (d i.succ))),
      I ∈ (D i.succ).cubes (sharpGeneration s a i.succ) →
      (I : Set (Fin (d i.succ) → ℝ)) ⊆ boxUnion (P i (a i).val) →
      volume.real ((I : Set (Fin (d i.succ) → ℝ)) ∩ boxUnion (P i ((a i).val + 1))) =
        (2 : ℝ) ^ (-(s : ℤ)) * volume.real (I : Set (Fin (d i.succ) → ℝ))) :
    ∃ E : (∀ j, Box (Fin (d j))) → Set (ProductPoint d),
      (∀ (a : Fin (n + 2) → Fin N) R, R ∈ sharpSpatialFamily s Q P a →
        E R = sharpSpatialWitness P a R) ∧
      (∀ R ∈ sharpSpatialTotal N s Q P,
        MeasurableSet (E R) ∧ E R ⊆ productBox R ∧
          volume.real (E R) = (1 - (2 : ℝ) ^ (-(s : ℤ))) ^ (n + 2) *
            volume.real (productBox R)) ∧
      Set.PairwiseDisjoint (↑(sharpSpatialTotal N s Q P) :
        Set (∀ j, Box (Fin (d j)))) E := by
  have hu := (sharpSpatialTotal_properties hN s hs hd D Q hQ P hP hPzero hPnest).2.2.2
  have hex (R : ∀ j, Box (Fin (d j))) :
      ∃ a : Fin (n + 2) → Fin N,
        R ∈ sharpSpatialTotal N s Q P → R ∈ sharpSpatialFamily s Q P a := by
    by_cases hR : R ∈ sharpSpatialTotal N s Q P
    · obtain ⟨a, ha, _⟩ := hu R hR
      exact ⟨a, fun _ => ha⟩
    · exact ⟨(fun _ => ⟨0, by omega⟩), fun h => (hR h).elim⟩
  choose idx hidx using hex
  refine ⟨fun R => sharpSpatialWitness P (idx R) R, ?_, ?_, ?_⟩
  · intro a R hR
    have hRT := mem_spatialTotal_of_mem hR
    obtain ⟨b, _, huniq⟩ := hu R hRT
    have ha : idx R = a := (huniq (idx R) (hidx R hRT)).trans (huniq a hR).symm
    exact congrArg (fun b : Fin (n + 2) → Fin N => sharpSpatialWitness P b R) ha
  · intro R hR
    exact sharpSpatialWitness_properties hN s D Q hQ P hP hlocal (idx R) R (hidx R hR)
  · intro R hR S hS hne
    by_cases hab : idx R = idx S
    · have hSi : S ∈ sharpSpatialFamily s Q P (idx R) := by
        simpa only [hab] using hidx S hS
      exact ((sharpSpatialFamily_partition hN s D Q hQ P hP (idx R)).2.2.1
        (hidx R hR) hSi hne).mono
          (spatialWitness_subset P (idx R) R) (spatialWitness_subset P (idx S) S)
    · exact spatialWitness_disjoint_of_ne hN s D Q hQ P hP hPnest
        (hidx R hR) (hidx S hS) hab

private theorem spatial_sum_by_index (hN : 2 ≤ N) (s : ℕ) (hs : 1 ≤ s)
    (hd : ∀ j, 0 < d j) (D : ∀ j, DyadicGrid (d j))
    (Q : ∀ j, Box (Fin (d j))) (hQ : ∀ j, Q j ∈ (D j).cubes 0)
    (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ))))
    (hP : ∀ i k R, R ∈ P i k →
      R ∈ (D i.succ).cubes ((s : ℤ) * selectionScale N i k))
    (hPzero : ∀ i, boxUnion (P i 0) = (Q i.succ : Set (Fin (d i.succ) → ℝ)))
    (hPnest : ∀ i k, boxUnion (P i (k + 1)) ⊆ boxUnion (P i k))
    (f : (∀ j, Box (Fin (d j))) → ℝ) :
    (∑ R ∈ sharpSpatialTotal N s Q P, f R) =
      ∑ a : Fin (n + 2) → Fin N, ∑ R ∈ sharpSpatialFamily s Q P a, f R := by
  have hu := (sharpSpatialTotal_properties hN s hs hd D Q hQ P hP hPzero hPnest).2.2.2
  have hdis : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin (n + 2) → Fin N)) : Set (Fin (n + 2) → Fin N))
      (sharpSpatialFamily s Q P) := by
    intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro R hRa hRb
    obtain ⟨c, _, huniq⟩ := hu R (mem_spatialTotal_of_mem hRa)
    exact hab ((huniq a hRa).trans (huniq b hRb).symm)
  exact Finset.sum_biUnion hdis

/-- The paper's overlap product, with each total-family rectangle
counted once and every index accounted for. -/
theorem sharpSpatialTotal_overlap (hN : 2 ≤ N) (s : ℕ) (hs : 1 ≤ s)
    (hd : ∀ j, 0 < d j) (D : ∀ j, DyadicGrid (d j))
    (Q : ∀ j, Box (Fin (d j))) (hQ : ∀ j, Q j ∈ (D j).cubes 0)
    (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ))))
    (hP : ∀ i k R, R ∈ P i k →
      R ∈ (D i.succ).cubes ((s : ℤ) * selectionScale N i k))
    (hPzero : ∀ i, boxUnion (P i 0) = (Q i.succ : Set (Fin (d i.succ) → ℝ)))
    (hPnest : ∀ i k, boxUnion (P i (k + 1)) ⊆ boxUnion (P i k))
    (x : ProductPoint d) :
    (∑ R ∈ sharpSpatialTotal N s Q P, (productBox R).indicator (fun _ => (1 : ℝ)) x) =
      (Q 0 : Set (Fin (d 0) → ℝ)).indicator (fun _ => (1 : ℝ)) (x 0) *
        ∏ i : Fin (n + 2), ∑ k : Fin N,
          (boxUnion (P i k.val)).indicator (fun _ => (1 : ℝ)) (x i.succ) := by
  rw [spatial_sum_by_index hN s hs hd D Q hQ P hP hPzero hPnest]
  have hfixed (a : Fin (n + 2) → Fin N) :=
    (sharpSpatialFamily_partition hN s D Q hQ P hP a).2.2.2 x
  simp_rw [hfixed]
  rw [← Finset.mul_sum]
  exact congrArg (fun z : ℝ =>
    (Q 0 : Set (Fin (d 0) → ℝ)).indicator (fun _ => (1 : ℝ)) (x 0) * z)
    (Fintype.prod_sum (fun (i : Fin (n + 2)) (k : Fin N) =>
      (boxUnion (P i k.val)).indicator (fun _ => (1 : ℝ)) (x i.succ))).symm

private theorem spatial_sum_indicator (hN : 2 ≤ N) (s : ℕ)
    (D : ∀ j, DyadicGrid (d j)) (Q : ∀ j, Box (Fin (d j)))
    (hQ : ∀ j, Q j ∈ (D j).cubes 0)
    (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ))))
    (hP : ∀ i k R, R ∈ P i k →
      R ∈ (D i.succ).cubes ((s : ℤ) * selectionScale N i k))
    (a : Fin (n + 2) → Fin N) (x : ProductPoint d) :
    (∑ R ∈ sharpSpatialFamily s Q P a, (productBox R).indicator (fun _ => (1 : ℝ)) x) =
      {y : ProductPoint d | y 0 ∈ Q 0 ∧
        ∀ i, y i.succ ∈ boxUnion (P i (a i).val)}.indicator (fun _ => (1 : ℝ)) x := by
  obtain ⟨_, hcover, hdis, _⟩ := sharpSpatialFamily_partition hN s D Q hQ P hP a
  by_cases hx : x ∈ {y : ProductPoint d | y 0 ∈ Q 0 ∧
      ∀ i, y i.succ ∈ boxUnion (P i (a i).val)}
  · have hxc : x ∈ ⋃ R ∈ sharpSpatialFamily s Q P a, productBox R := by
      rw [hcover]
      exact hx
    obtain ⟨R, hxR⟩ := Set.mem_iUnion.mp hxc
    obtain ⟨hR, hxR⟩ := Set.mem_iUnion.mp hxR
    rw [Finset.sum_eq_single R]
    · simp only [Set.indicator_of_mem hxR, Set.indicator_of_mem hx]
    · intro S hS hSR
      exact Set.indicator_of_notMem
        (fun hxS => Set.disjoint_left.mp (hdis hS hR hSR) hxS hxR) _
    · intro hnot
      exact (hnot hR).elim
  · rw [Set.indicator_of_notMem hx]
    apply Finset.sum_eq_zero
    intro R hR
    apply Set.indicator_of_notMem
    intro hxR
    apply hx
    rw [← hcover]
    exact Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨hR, hxR⟩⟩

/-- The maximum-overlap set is exactly the deepest retained product set,
not just a subset or an almost-everywhere representative. -/
theorem sharpSpatialTotal_maximum_set (hN : 2 ≤ N) (s : ℕ) (hs : 1 ≤ s)
    (hd : ∀ j, 0 < d j) (D : ∀ j, DyadicGrid (d j))
    (Q : ∀ j, Box (Fin (d j))) (hQ : ∀ j, Q j ∈ (D j).cubes 0)
    (P : ∀ i : Fin (n + 2), ℕ → Finset (Box (Fin (d i.succ))))
    (hP : ∀ i k R, R ∈ P i k →
      R ∈ (D i.succ).cubes ((s : ℤ) * selectionScale N i k))
    (hPzero : ∀ i, boxUnion (P i 0) = (Q i.succ : Set (Fin (d i.succ) → ℝ)))
    (hPnest : ∀ i k, boxUnion (P i (k + 1)) ⊆ boxUnion (P i k)) :
    {x : ProductPoint d | (∑ R ∈ sharpSpatialTotal N s Q P,
      (productBox R).indicator (fun _ => (1 : ℝ)) x) = (N : ℝ) ^ (n + 2)} =
      {x : ProductPoint d | x 0 ∈ Q 0 ∧
        ∀ i, x i.succ ∈ boxUnion (P i (N - 1))} := by
  let U (a : Fin (n + 2) → Fin N) : Set (ProductPoint d) :=
    {x | x 0 ∈ Q 0 ∧ ∀ i, x i.succ ∈ boxUnion (P i (a i).val)}
  have hsum (x : ProductPoint d) :
      (∑ R ∈ sharpSpatialTotal N s Q P, (productBox R).indicator (fun _ => (1 : ℝ)) x) =
        ∑ a : Fin (n + 2) → Fin N, (U a).indicator (fun _ => (1 : ℝ)) x := by
    rw [spatial_sum_by_index hN s hs hd D Q hQ P hP hPzero hPnest]
    exact Finset.sum_congr rfl (fun a _ => spatial_sum_indicator hN s D Q hQ P hP a x)
  have hcard : (∑ _a : Fin (n + 2) → Fin N, (1 : ℝ)) = (N : ℝ) ^ (n + 2) := by
    simp
  ext x
  change (∑ R ∈ sharpSpatialTotal N s Q P,
    (productBox R).indicator (fun _ => (1 : ℝ)) x) = (N : ℝ) ^ (n + 2) ↔ _
  rw [hsum x]
  constructor
  · intro hx
    have hle (a : Fin (n + 2) → Fin N) :
        (U a).indicator (fun _ => (1 : ℝ)) x ≤ 1 := by
      by_cases ha : x ∈ U a <;> simp [ha]
    have hall := (Finset.sum_eq_sum_iff_of_le
      (s := (Finset.univ : Finset (Fin (n + 2) → Fin N)))
      (fun a _ => hle a)).mp (hx.trans hcard.symm)
    let aM : Fin (n + 2) → Fin N := fun _ => ⟨N - 1, by omega⟩
    have hM := hall aM (Finset.mem_univ aM)
    have hxM : x ∈ U aM := by
      by_contra h
      rw [Set.indicator_of_notMem h] at hM
      norm_num at hM
    exact hxM
  · intro hx
    have hmem (a : Fin (n + 2) → Fin N) : x ∈ U a := by
      refine ⟨hx.1, ?_⟩
      intro i
      have hval : (a i).val ≤ N - 1 := by omega
      have hm : Antitone (fun k => boxUnion (P i k)) :=
        antitone_nat_of_succ_le (hPnest i)
      exact hm hval (hx.2 i)
    calc
      _ = ∑ _a : Fin (n + 2) → Fin N, (1 : ℝ) :=
        Finset.sum_congr rfl (fun a _ => Set.indicator_of_mem (hmem a) _)
      _ = _ := hcard

end ReyZygmund.Sharpness
