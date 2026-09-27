import ReyZygmund.Sharpness.Construction
import ReyZygmund.Overlap.FiniteIdentification

/-! # Ordinary-coordinate realization of the sharpness family

The coordinate equivalence preserves sets, indicators, disjointness
and Lebesgue measure. In particular, the maximum-overlap set in the concrete
construction has its asserted mass in the ordinary Euclidean space as well.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Sharpness

open Geometry Overlap

variable {m : ℕ} {d : Fin m → ℕ}

theorem volume_flatten_set (A : Set (ProductPoint d)) :
    volume ((flattenCoordinates d).symm ⁻¹' A) = volume A := by
  rw [← (volume_preserving_flattenCoordinates d).map_eq,
    MeasurableEquiv.map_apply]
  congr 1
  ext x
  simp only [Set.mem_preimage, MeasurableEquiv.symm_apply_apply]

theorem finiteShadow_flatten (G : Finset (∀ i, Box (Fin (d i)))) :
    (flattenCoordinates d) ⁻¹' finiteShadow G = ⋃ R ∈ G, productBox R := by
  ext x
  simp only [finiteShadow, Set.mem_preimage, Set.mem_iUnion, Box.mem_coe, mem_flatProductBox]

theorem finiteOverlap_flatten (G : Finset (∀ i, Box (Fin (d i))))
    (x : ProductPoint d) :
    finiteOverlap G (flattenCoordinates d x) =
      ∑ R ∈ G, (productBox R).indicator (fun _ => (1 : ℝ)) x := by
  apply Finset.sum_congr rfl
  intro R _
  have hmem : flattenCoordinates d x ∈ (flatProductBox R : Set _) ↔ x ∈ productBox R := by
    simp only [Box.mem_coe, mem_flatProductBox]
  by_cases hx : x ∈ productBox R
  · simp only [Set.indicator_of_mem hx,
      Set.indicator_of_mem (hmem.mpr hx)]
  · simp only [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (fun h => hx (hmem.mp h))]

theorem volume_zero_generation_product (D : ∀ i, DyadicGrid (d i))
    (Q : ∀ i, Box (Fin (d i))) (hQ : ∀ i, Q i ∈ (D i).cubes 0) :
    volume (productBox Q) = 1 := by
  have hreal (i : Fin m) : volume.real (Q i : Set (Fin (d i) → ℝ)) = 1 := by
    simp only [measureReal_def, Box.volume_apply']
    simp_rw [(D i).width 0 (Q i) (hQ i)]
    simp
  have hvol (i : Fin m) : volume (Q i : Set (Fin (d i) → ℝ)) = 1 := by
    calc
      volume (Q i : Set (Fin (d i) → ℝ)) =
          ENNReal.ofReal (volume.real (Q i : Set (Fin (d i) → ℝ))) :=
        (ENNReal.ofReal_toReal ((Q i).measure_coe_lt_top volume).ne).symm
      _ = 1 := by rw [hreal, ENNReal.ofReal_one]
  change Measure.pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
    (Set.pi Set.univ (fun i => (Q i : Set (Fin (d i) → ℝ)))) = 1
  rw [Measure.pi_pi]
  simp_rw [hvol]
  simp

/-- All conclusions are now for the ordinary-coordinate rectangles and
their finite overlap. The sparse fraction is still exact. -/
theorem exists_sharp_flat_construction (n N s : ℕ) (hN : 2 ≤ N) (hs : 1 ≤ s)
    (d : Fin (n + 3) → ℕ) (hd : ∀ j, 0 < d j)
    (D : ∀ j, DyadicGrid (d j)) :
    ∃ G : Finset (∀ j, Box (Fin (d j))),
      ∃ E : (∀ j, Box (Fin (d j))) → Set (Fin (∑ j, d j) → ℝ),
        ∃ L : Set (Fin (∑ j, d j) → ℝ),
      (↑G : Set (∀ j, Box (Fin (d j)))) ⊆
        Continuous.dyadicPhiRectangles D (fun k : Fin (n + 2) → ℤ => ∑ i, k i) ∧
      (∀ R ∈ G, ∀ S ∈ G,
        (flatProductBox R : Set (Fin (∑ j, d j) → ℝ)) ⊆ flatProductBox S → R = S) ∧
      volume (finiteShadow G) = 1 ∧
      (∀ R ∈ G, MeasurableSet (E R) ∧ E R ⊆ flatProductBox R ∧
        volume.real (E R) = (1 - (2 : ℝ) ^ (-(s : ℤ))) ^ (n + 2) *
          volume.real (flatProductBox R : Set (Fin (∑ j, d j) → ℝ))) ∧
      Set.PairwiseDisjoint (↑G : Set (∀ j, Box (Fin (d j)))) E ∧
      MeasurableSet L ∧ L ⊆ finiteShadow G ∧
      (∀ x ∈ L, finiteOverlap G x = (N : ℝ) ^ (n + 2)) ∧
      volume.real L = ((2 : ℝ) ^ (-(s : ℤ))) ^ ((n + 2) * (N - 1)) := by
  have hroots (j : Fin (n + 3)) : ∃ Q, Q ∈ (D j).cubes 0 := by
    obtain ⟨Q, hQ, _⟩ := (D j).cover 0 0
    exact ⟨Q, hQ⟩
  choose Q hQ using hroots
  obtain ⟨G, E, L, hG, hinc, hshadow, hE, hdis, hLm, hLs, hlevel, hmass⟩ :=
    exists_sharp_spatial_construction n N s hN hs d hd D Q hQ
  let e := flattenCoordinates d
  have hroot := volume_zero_generation_product D Q hQ
  refine ⟨G, (fun R => e.symm ⁻¹' E R), e.symm ⁻¹' L, hG, ?_, ?_, ?_, ?_,
    hLm.preimage e.symm.measurable, ?_, ?_, ?_⟩
  · intro R hR S hS hRS
    apply hinc R hR S hS
    intro x hx
    exact (mem_flatProductBox S x).mp (hRS ((mem_flatProductBox R x).mpr hx))
  · have hpre := (finiteShadow_flatten G).trans hshadow
    calc
      volume (finiteShadow G) =
          volume ((flattenCoordinates d) ⁻¹' finiteShadow G) := by
        rw [← (volume_preserving_flattenCoordinates d).map_eq, MeasurableEquiv.map_apply]
      _ = 1 := by rw [hpre, hroot]
  · intro R hR
    refine ⟨(hE R hR).1.preimage e.symm.measurable, ?_, ?_⟩
    · intro x hx
      have hy := (hE R hR).2.1 hx
      simpa only [e, Box.mem_coe, MeasurableEquiv.apply_symm_apply] using
        (mem_flatProductBox R (e.symm x)).mpr hy
    · simp only [e, measureReal_def, volume_flatten_set, volume_flatProductBox]
      exact (hE R hR).2.2
  · intro R hR S hS hRS
    exact (hdis hR hS hRS).preimage e.symm
  · intro x hx
    have hy := hLs hx
    have : e.symm x ∈ e ⁻¹' finiteShadow G := by
      rw [finiteShadow_flatten]
      exact hy
    simpa only [Set.mem_preimage, MeasurableEquiv.apply_symm_apply] using this
  · intro x hx
    have hy : (∑ R ∈ G, (productBox R).indicator (fun _ => (1 : ℝ)) (e.symm x)) =
        (N : ℝ) ^ (n + 2) := by
      rw [hlevel] at hx
      exact hx
    simpa only [e, MeasurableEquiv.apply_symm_apply] using
      (finiteOverlap_flatten G (e.symm x)).trans hy
  · simpa only [e, measureReal_def, volume_flatten_set, hroot,
      ENNReal.toReal_one, mul_one] using hmass

end ReyZygmund.Sharpness
