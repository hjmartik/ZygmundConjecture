import ReyZygmund.Geometry.GridOrder
import ReyZygmund.Geometry.FiniteDifferenceAlgebra

/-! # Average and difference identities on a dyadic grid

Intersecting dyadic cubes have a common containing cube; support handles the
disjoint case. The identities use the children of every cube under consideration.
A common ancestor for the whole grid is not assumed.
-/

open BoxIntegral MeasureTheory
open scoped Classical

namespace ReyZygmund.Geometry

variable {d : ℕ}

theorem grid_child_of_strict_containment (hd : 0 < d) (D : DyadicGrid d)
    {a b : ℤ} {L Q : Box (Fin d)} (hL : L ∈ D.cubes a) (hQ : Q ∈ D.cubes b)
    (hlt : L < Q) : ∃ J, J ∈ Prepartition.splitCenter Q ∧ L ≤ J := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hba := D.generation_lt_of_containment_ne hL hQ hlt.le hlt.ne
  have hindex : b + ((a - b).toNat : ℤ) = a := by omega
  have hlocal : L ∈ level Q (a - b).toNat :=
    (D.mem_level_iff hQ).mpr ⟨by simpa only [hindex] using hL, hlt.le⟩
  have hLd : L ∈ descendants Q (a - b).toNat :=
    mem_descendants.mpr ⟨_, le_rfl, hlocal⟩
  have hQd : Q ∈ descendants Q (a - b).toNat :=
    mem_descendants.mpr ⟨0, Nat.zero_le _, by simp⟩
  obtain ⟨J, hJ, _⟩ := DifferenceAlgebra.exists_unique_child_of_lt hLd hQd hlt
  exact ⟨J, hJ⟩

/-- Full one-coordinate source identity, with only the integral on
the inner difference's support required. Equality is in the zero branch. -/
theorem grid_average_difference (hd : 0 < d) (D : DyadicGrid d)
    {a b : ℤ} (L Q : Box (Fin d)) (hL : L ∈ D.cubes a) (hQ : Q ∈ D.cubes b)
    (f : (Fin d → ℝ) → ℝ) (hf : IntegrableOn f (Q : Set (Fin d → ℝ)) volume) :
    boxAverage L (boxDifference Q f) =
      if L < Q then (L : Set (Fin d → ℝ)).indicator (boxDifference Q f) else 0 := by
  by_cases hlt : L < Q
  · rw [ite_eq_left hlt]
    obtain ⟨J, hJ, hLJ⟩ := grid_child_of_strict_containment hd D hL hQ hlt
    exact DifferenceAlgebra.boxAverage_boxDifference_of_le_child hJ hLJ f
  · rw [ite_eq_right hlt]
    by_cases hdis : Disjoint (L : Set (Fin d → ℝ)) Q
    · exact DifferenceAlgebra.boxAverage_boxDifference_of_disjoint hdis f
    · have hex : ∃ x, x ∈ L ∧ x ∈ Q := by
        simpa only [Set.disjoint_left, not_forall, not_not, exists_prop, Box.mem_coe] using hdis
      obtain ⟨x, hxL, hxQ⟩ := hex
      rcases D.nested_of_common_point hL hQ hxL hxQ with hLQ | hQL
      · have heq : L = Q := (lt_or_eq_of_le hLQ).resolve_left hlt
        subst L
        exact DifferenceAlgebra.boxAverage_boxDifference_of_le le_rfl f hf
      · exact DifferenceAlgebra.boxAverage_boxDifference_of_le hQL f hf

/-- Full one-coordinate orthogonality, including equality, disjoint cubes,
and negative generations. -/
theorem grid_difference_difference (hd : 0 < d) (D : DyadicGrid d)
    {a b : ℤ} (L Q : Box (Fin d)) (hL : L ∈ D.cubes a) (hQ : Q ∈ D.cubes b)
    (f : (Fin d → ℝ) → ℝ) (hf : IntegrableOn f (Q : Set (Fin d → ℝ)) volume) :
    boxDifference L (boxDifference Q f) =
      if L = Q then boxDifference Q f else 0 := by
  by_cases heq : L = Q
  · subst L
    rw [ite_eq_left rfl]
    exact DifferenceAlgebra.boxDifference_boxDifference_self Q f hf
  · rw [ite_eq_right heq]
    by_cases hdis : Disjoint (L : Set (Fin d → ℝ)) Q
    · exact DifferenceAlgebra.boxDifference_boxDifference_of_disjoint hdis f
    · have hex : ∃ x, x ∈ L ∧ x ∈ Q := by
        simpa only [Set.disjoint_left, not_forall, not_not, exists_prop, Box.mem_coe] using hdis
      obtain ⟨x, hxL, hxQ⟩ := hex
      rcases D.nested_of_common_point hL hQ hxL hxQ with hLQ | hQL
      · obtain ⟨J, hJ, hLJ⟩ := grid_child_of_strict_containment hd D hL hQ
          (lt_of_le_of_ne hLQ heq)
        exact DifferenceAlgebra.boxDifference_boxDifference_of_le_child hJ hLJ f
      · obtain ⟨J, hJ, hQJ⟩ := grid_child_of_strict_containment hd D hQ hL
          (lt_of_le_of_ne hQL (Ne.symm heq))
        exact DifferenceAlgebra.boxDifference_boxDifference_of_parent_le_child hJ hQJ f hf

end ReyZygmund.Geometry
