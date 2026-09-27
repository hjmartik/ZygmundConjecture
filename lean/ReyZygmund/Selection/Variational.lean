import ReyZygmund.Overlap.Finite
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith

/-! # Finite variational selection

Maximize twice the shadow's volume minus the sum of rectangle volumes. Deletion
and insertion give the weak half-volume inequalities. Differences of measurable
finite shadows give the disjoint subsets establishing sparseness. The construction
needs neither grids nor positive coordinate dimensions; `Shadow.lean` proves the
analytic shadow bound.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Selection

open Geometry Overlap

variable {m : ℕ} {d : Fin m → ℕ}

private theorem finiteShadow_insert
    (G : Finset (∀ i, Box (Fin (d i)))) (Q : ∀ i, Box (Fin (d i))) :
    finiteShadow (insert Q G) = (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∪ finiteShadow G := by
  ext x
  simp only [finiteShadow, Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
  constructor
  · rintro ⟨R, hR, hx⟩
    rcases hR with rfl | hR
    · exact Or.inl hx
    · exact Or.inr ⟨R, hR, hx⟩
  · rintro (hx | ⟨R, hR, hx⟩)
    · exact ⟨Q, Or.inl rfl, hx⟩
    · exact ⟨R, Or.inr hR, hx⟩

private theorem finiteShadow_insert_volume
    (G : Finset (∀ i, Box (Fin (d i)))) (Q : ∀ i, Box (Fin (d i))) :
    volume.real (finiteShadow (insert Q G)) +
        volume.real ((flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∩ finiteShadow G) =
      volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) + volume.real (finiteShadow G) := by
  rw [finiteShadow_insert]
  exact measureReal_union_add_inter (measurableSet_finiteShadow G)
    (flatProductBox Q).isBounded.measure_lt_top.ne (volume_finiteShadow_lt_top G).ne

/-- A maximizing subfamily satisfies deletion half-overlap and insertion
half-density for the Euclidean rectangles. The maximum is over all
subfamilies, including the empty one. -/
theorem finite_variational_selection
    (F : Finset (∀ i, Box (Fin (d i)))) :
    ∃ G : Finset (∀ i, Box (Fin (d i))), G ⊆ F ∧
      (∀ V : Finset (∀ i, Box (Fin (d i))), V ⊆ F →
        2 * volume.real (finiteShadow V) -
            ∑ Q ∈ V, volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ≤
          2 * volume.real (finiteShadow G) -
            ∑ Q ∈ G, volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ))) ∧
      (∀ Q ∈ G,
        volume.real ((flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∩ finiteShadow (G.erase Q)) ≤
          (1 / 2 : ℝ) * volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ))) ∧
      (∀ Q ∈ F,
        (1 / 2 : ℝ) * volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ≤
          volume.real ((flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∩ finiteShadow G)) := by
  let score : Finset (∀ i, Box (Fin (d i))) → ℝ := fun V =>
    2 * volume.real (finiteShadow V) - ∑ Q ∈ V, volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ))
  obtain ⟨G, hG, hmax⟩ := Finset.exists_max_image F.powerset score F.powerset_nonempty
  have hGF : G ⊆ F := Finset.mem_powerset.mp hG
  refine ⟨G, hGF, ?_, ?_, ?_⟩
  · intro V hV
    exact hmax V (Finset.mem_powerset.mpr hV)
  · intro Q hQ
    have hdel := hmax (G.erase Q)
      (Finset.mem_powerset.mpr ((Finset.erase_subset Q G).trans hGF))
    have hvol := finiteShadow_insert_volume (G.erase Q) Q
    rw [Finset.insert_erase hQ] at hvol
    have hsum := Finset.add_sum_erase G
      (fun R => volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) hQ
    dsimp only [score] at hdel
    linarith
  · intro Q hQ
    by_cases hQG : Q ∈ G
    · have hset : (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∩ finiteShadow G =
          (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) :=
        Set.inter_eq_left.mpr (flatProductBox_subset_finiteShadow G Q hQG)
      rw [hset]
      have hnonneg : 0 ≤ volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) := measureReal_nonneg
      linarith
    · have hinsub : insert Q G ⊆ F := by
        intro R hR
        rcases Finset.mem_insert.mp hR with rfl | hR
        · exact hQ
        · exact hGF hR
      have hins := hmax (insert Q G) (Finset.mem_powerset.mpr hinsub)
      have hvol := finiteShadow_insert_volume G Q
      have hsum : (∑ R ∈ insert Q G, volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) =
          volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) +
            ∑ R ∈ G, volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) := Finset.sum_insert hQG
      dsimp only [score] at hins
      linarith

/-- The selected rectangles contain measurable pairwise disjoint subsets of at least
half their volume. The insertion-density bound holds for every original rectangle.
-/
theorem finite_variational_half_sparse
    (F : Finset (∀ i, Box (Fin (d i)))) :
    ∃ G : Finset (∀ i, Box (Fin (d i))), G ⊆ F ∧
      (∀ Q ∈ G,
        volume.real ((flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∩ finiteShadow (G.erase Q)) ≤
          (1 / 2 : ℝ) * volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ))) ∧
      (∀ Q ∈ F,
        (1 / 2 : ℝ) * volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ≤
          volume.real ((flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∩ finiteShadow G)) ∧
      ∃ E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ),
        (∀ Q, E Q = (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) \ finiteShadow (G.erase Q)) ∧
        (∀ Q ∈ G, MeasurableSet (E Q) ∧ E Q ⊆ (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∧
          (1 / 2 : ℝ) * volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ≤ volume.real (E Q)) ∧
        Set.Pairwise (↑G : Set (∀ i, Box (Fin (d i))))
          (fun Q R => Disjoint (E Q) (E R)) := by
  obtain ⟨G, hGF, _hmax, hoverlap, hdensity⟩ := finite_variational_selection F
  let E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ) := fun Q =>
    (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) \ finiteShadow (G.erase Q)
  refine ⟨G, hGF, hoverlap, hdensity, E, fun _ => rfl, ?_, ?_⟩
  · intro Q hQ
    refine ⟨(flatProductBox Q).measurableSet_coe.diff
      (measurableSet_finiteShadow (G.erase Q)), Set.sdiff_subset, ?_⟩
    have hvol := measureReal_inter_add_sdiff (μ := volume)
      (s := (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ))) (measurableSet_finiteShadow (G.erase Q))
      (flatProductBox Q).isBounded.measure_lt_top.ne
    have hhalf := hoverlap Q hQ
    change (1 / 2 : ℝ) * volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ≤
      volume.real ((flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) \ finiteShadow (G.erase Q))
    linarith
  · intro Q _hQ R hR hne
    apply Set.disjoint_left.mpr
    intro x hxQ hxR
    have hxQ' : x ∈ (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∧ x ∉ finiteShadow (G.erase Q) := hxQ
    have hxR' : x ∈ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ∧ x ∉ finiteShadow (G.erase R) := hxR
    exact hxQ'.2 (flatProductBox_subset_finiteShadow (G.erase Q) R
      (Finset.mem_erase.mpr ⟨Ne.symm hne, hR⟩) hxR'.1)

end ReyZygmund.Selection
