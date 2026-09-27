import ReyZygmund.Sharpness.Retention
import ReyZygmund.Geometry.GridOrder

/-! # One retention step over a finite grid partition

All unions below are unions of half-open boxes. The retained family
will be constructed from the proved one-box retention lemma; local fractions
are derived from the grid containment and disjointness properties.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Sharpness

open Geometry

/-- The union of a finite family of boxes. -/
def boxUnion {d : ℕ} (P : Finset (Box (Fin d))) : Set (Fin d → ℝ) :=
  ⋃ Q ∈ P, (Q : Set (Fin d → ℝ))

theorem measurableSet_boxUnion {d : ℕ} (P : Finset (Box (Fin d))) :
    MeasurableSet (boxUnion P) :=
  Finset.measurableSet_biUnion P (fun Q _ => Q.measurableSet_coe)

theorem volume_boxUnion_lt_top {d : ℕ} (P : Finset (Box (Fin d))) :
    volume (boxUnion P) < ⊤ := by
  apply measure_biUnion_lt_top P.finite_toSet
  intro Q _
  exact Q.measure_coe_lt_top volume

private theorem boxUnion_biUnion {d : ℕ} (P : Finset (Box (Fin d)))
    (T : Box (Fin d) → Finset (Box (Fin d))) :
    boxUnion (P.biUnion T) = ⋃ Q ∈ P, boxUnion (T Q) := by
  ext x
  simp only [boxUnion, Set.mem_iUnion, Finset.mem_biUnion]
  constructor
  · rintro ⟨R, ⟨Q, hQ, hR⟩, hxR⟩
    exact ⟨Q, hQ, R, hR, hxR⟩
  · rintro ⟨Q, hQ, R, hR, hxR⟩
    exact ⟨R, ⟨Q, hQ, hR⟩, hxR⟩

/-- Finite refinement preserves the union pointwise, including boundaries. Neither a
common top cube nor disjointness is needed. -/
theorem boxUnion_level_biUnion {d : ℕ} (P : Finset (Box (Fin d))) (t : ℕ) :
    boxUnion (P.biUnion (fun Q => (level Q t).boxes)) = boxUnion P := by
  rw [boxUnion_biUnion]
  have hlevel (Q : Box (Fin d)) : boxUnion (level Q t).boxes =
      (Q : Set (Fin d → ℝ)) := by
    change (level Q t).iUnion = _
    exact (level_isPartition Q t).iUnion_eq
  simp_rw [hlevel]
  rfl

private theorem volume_inter_biUnion {d : ℕ} (P : Finset (Box (Fin d)))
    (T : Box (Fin d) → Set (Fin d → ℝ))
    (hdis : Set.PairwiseDisjoint (↑P : Set (Box (Fin d))) T)
    (hmeas : ∀ Q ∈ P, MeasurableSet (T Q))
    (hfin : ∀ Q ∈ P, volume (T Q) < ⊤) (I : Box (Fin d)) :
    volume.real ((I : Set (Fin d → ℝ)) ∩ ⋃ Q ∈ P, T Q) =
      ∑ Q ∈ P, volume.real ((I : Set (Fin d → ℝ)) ∩ T Q) := by
  simp_rw [Set.inter_iUnion]
  apply measureReal_biUnion_finset
  · intro Q hQ R hR hne
    exact (hdis hQ hR hne).mono Set.inter_subset_right Set.inter_subset_right
  · intro Q hQ
    exact I.measurableSet_coe.inter (hmeas Q hQ)
  · intro Q hQ
    exact ((measure_mono Set.inter_subset_right).trans_lt (hfin Q hQ)).ne

private theorem local_fraction_of_grid_order {d : ℕ} (D : DyadicGrid d)
    {n k : ℤ} {Q I : Box (Fin d)} (hQ : Q ∈ D.cubes n)
    (hI : I ∈ D.cubes k) (hkn : k ≤ n) (U : Set (Fin d → ℝ))
    (hU : U ⊆ (Q : Set (Fin d → ℝ))) (c : ℝ)
    (hmass : volume.real U = c * volume.real (Q : Set (Fin d → ℝ))) :
    volume.real ((I : Set (Fin d → ℝ)) ∩ U) =
      c * volume.real ((I : Set (Fin d → ℝ)) ∩ (Q : Set (Fin d → ℝ))) := by
  by_cases hQI : Q ≤ I
  · have hsub : (Q : Set (Fin d → ℝ)) ⊆ (I : Set (Fin d → ℝ)) := hQI
    have hUsub : U ⊆ (I : Set (Fin d → ℝ)) := hU.trans hsub
    have hIU : (I : Set (Fin d → ℝ)) ∩ U = U := Set.inter_eq_right.mpr hUsub
    have hIQ : (I : Set (Fin d → ℝ)) ∩ (Q : Set (Fin d → ℝ)) =
        (Q : Set (Fin d → ℝ)) := Set.inter_eq_right.mpr hsub
    rw [hIU, hIQ]
    exact hmass
  · have hdis : Disjoint (I : Set (Fin d → ℝ)) (Q : Set (Fin d → ℝ)) := by
      apply Set.disjoint_left.mpr
      intro x hxI hxQ
      exact hQI (D.le_of_generation_le hI hQ hkn hxI hxQ)
    rw [Set.disjoint_iff_inter_eq_empty.mp (hdis.mono_right hU),
      Set.disjoint_iff_inter_eq_empty.mp hdis]
    simp

/-- Retain the same exact fraction in each member of a finite grid partition.
Every coarser same-grid box sees that fraction of its original intersection. -/
theorem exists_retained_partition {d : ℕ} (hd : 0 < d) (D : DyadicGrid d)
    (n : ℤ) (P : Finset (Box (Fin d))) (hP : ∀ Q ∈ P, Q ∈ D.cubes n) (s : ℕ) :
    ∃ F : Finset (Box (Fin d)),
      F ⊆ P.biUnion (fun Q => (level Q s).boxes) ∧
      (∀ R ∈ F, R ∈ D.cubes (n + (s : ℤ))) ∧
      Set.PairwiseDisjoint (↑F : Set (Box (Fin d))) (fun R => (R : Set (Fin d → ℝ))) ∧
      boxUnion F ⊆ boxUnion P ∧
      MeasurableSet (boxUnion F) ∧
      volume (boxUnion F) < ⊤ ∧
      volume.real (boxUnion F) = (2 : ℝ) ^ (-(s : ℤ)) * volume.real (boxUnion P) ∧
      ∀ (k : ℤ), k ≤ n → ∀ I ∈ D.cubes k,
        volume.real ((I : Set (Fin d → ℝ)) ∩ boxUnion F) =
          (2 : ℝ) ^ (-(s : ℤ)) *
            volume.real ((I : Set (Fin d → ℝ)) ∩ boxUnion P) := by
  have hret (Q : Box (Fin d)) : ∃ T : Finset (Box (Fin d)),
      T ⊆ (level Q s).boxes ∧
      boxUnion T ⊆ (Q : Set (Fin d → ℝ)) ∧
      volume.real (boxUnion T) =
        (2 : ℝ) ^ (-(s : ℤ)) * volume.real (Q : Set (Fin d → ℝ)) := by
    obtain ⟨T, hT, _, _, hsub, _, _, _, hmass⟩ := exists_retained_level hd Q s
    exact ⟨T, hT, hsub, hmass⟩
  let T (Q : Box (Fin d)) : Finset (Box (Fin d)) := Classical.choose (hret Q)
  have hTlevel (Q : Box (Fin d)) : T Q ⊆ (level Q s).boxes :=
    (Classical.choose_spec (hret Q)).1
  have hTsub (Q : Box (Fin d)) : boxUnion (T Q) ⊆ (Q : Set (Fin d → ℝ)) :=
    (Classical.choose_spec (hret Q)).2.1
  have hTmass (Q : Box (Fin d)) : volume.real (boxUnion (T Q)) =
      (2 : ℝ) ^ (-(s : ℤ)) * volume.real (Q : Set (Fin d → ℝ)) :=
    (Classical.choose_spec (hret Q)).2.2
  let F : Finset (Box (Fin d)) := P.biUnion T
  have hFlevel : F ⊆ P.biUnion (fun Q => (level Q s).boxes) := by
    intro R hR
    obtain ⟨Q, hQ, hRQ⟩ := Finset.mem_biUnion.mp hR
    exact Finset.mem_biUnion.mpr ⟨Q, hQ, hTlevel Q hRQ⟩
  have hgrid (R : Box (Fin d)) (hR : R ∈ F) : R ∈ D.cubes (n + (s : ℤ)) := by
    obtain ⟨Q, hQ, hRQ⟩ := Finset.mem_biUnion.mp (hFlevel hR)
    exact D.mem_cubes_of_mem_level (hP Q hQ) hRQ
  have hFdis : Set.PairwiseDisjoint (↑F : Set (Box (Fin d)))
      (fun R => (R : Set (Fin d → ℝ))) := by
    intro R hR S hS hne
    exact D.disjoint (n + (s : ℤ)) (hgrid R hR) (hgrid S hS) hne
  have hsub : boxUnion F ⊆ boxUnion P := by
    intro x hx
    simp only [boxUnion, Set.mem_iUnion] at hx ⊢
    obtain ⟨R, hR, hxR⟩ := hx
    obtain ⟨Q, hQ, hRQ⟩ := Finset.mem_biUnion.mp (hFlevel hR)
    exact ⟨Q, hQ, (level Q s).le_of_mem hRQ hxR⟩
  have hPdis : Set.PairwiseDisjoint (↑P : Set (Box (Fin d)))
      (fun Q => (Q : Set (Fin d → ℝ))) := by
    intro Q hQ R hR hne
    exact D.disjoint n (hP Q hQ) (hP R hR) hne
  have hTdis : Set.PairwiseDisjoint (↑P : Set (Box (Fin d)))
      (fun Q => boxUnion (T Q)) := by
    intro Q hQ R hR hne
    exact (hPdis hQ hR hne).mono (hTsub Q) (hTsub R)
  have hPvol : volume.real (boxUnion P) =
      ∑ Q ∈ P, volume.real (Q : Set (Fin d → ℝ)) :=
    measureReal_biUnion_finset hPdis (fun Q _ => Q.measurableSet_coe)
      (fun Q _ => (Q.measure_coe_lt_top volume).ne)
  have hmass : volume.real (boxUnion F) =
      (2 : ℝ) ^ (-(s : ℤ)) * volume.real (boxUnion P) := by
    change volume.real (boxUnion (P.biUnion T)) = _
    rw [boxUnion_biUnion]
    calc
      _ = ∑ Q ∈ P, volume.real (boxUnion (T Q)) :=
        measureReal_biUnion_finset hTdis (fun Q _ => measurableSet_boxUnion (T Q))
          (fun Q _ => (volume_boxUnion_lt_top (T Q)).ne)
      _ = ∑ Q ∈ P, (2 : ℝ) ^ (-(s : ℤ)) * volume.real (Q : Set (Fin d → ℝ)) :=
        Finset.sum_congr rfl (fun Q _ => hTmass Q)
      _ = (2 : ℝ) ^ (-(s : ℤ)) *
          (∑ Q ∈ P, volume.real (Q : Set (Fin d → ℝ))) := by rw [Finset.mul_sum]
      _ = _ := by rw [hPvol]
  refine ⟨F, hFlevel, hgrid, hFdis, hsub, measurableSet_boxUnion F,
    volume_boxUnion_lt_top F, hmass, ?_⟩
  intro k hkn I hI
  change volume.real ((I : Set (Fin d → ℝ)) ∩ boxUnion (P.biUnion T)) = _
  rw [boxUnion_biUnion]
  calc
    _ = ∑ Q ∈ P, volume.real ((I : Set (Fin d → ℝ)) ∩ boxUnion (T Q)) :=
      volume_inter_biUnion P (fun Q => boxUnion (T Q)) hTdis
        (fun Q _ => measurableSet_boxUnion (T Q))
        (fun Q _ => volume_boxUnion_lt_top (T Q)) I
    _ = ∑ Q ∈ P, (2 : ℝ) ^ (-(s : ℤ)) *
        volume.real ((I : Set (Fin d → ℝ)) ∩ (Q : Set (Fin d → ℝ))) :=
      Finset.sum_congr rfl (fun Q hQ => local_fraction_of_grid_order D
        (hP Q hQ) hI hkn (boxUnion (T Q)) (hTsub Q) _ (hTmass Q))
    _ = (2 : ℝ) ^ (-(s : ℤ)) *
        (∑ Q ∈ P, volume.real ((I : Set (Fin d → ℝ)) ∩ (Q : Set (Fin d → ℝ)))) := by
      rw [Finset.mul_sum]
    _ = _ := by
      congr 1
      exact (volume_inter_biUnion P (fun Q => (Q : Set (Fin d → ℝ))) hPdis
        (fun Q _ => Q.measurableSet_coe) (fun Q _ => Q.measure_coe_lt_top volume) I).symm

end ReyZygmund.Sharpness
