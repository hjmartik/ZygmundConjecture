import ReyZygmund.Geometry.FiniteCrossAverage

/-! # Averages and differences on a finite dyadic grid

The differences are sums of child averages minus the parent average. This
definition also applies at the smallest retained scale and uses the next
generation of children. We prove the average–difference identities and
one-coordinate orthogonality.

-/

noncomputable section

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry
namespace DifferenceAlgebra

variable {d : ℕ}

theorem boxAverage_eq_zero_of_notMem (Q : Box (Fin d)) (f : (Fin d → ℝ) → ℝ)
    {x : Fin d → ℝ} (hx : x ∉ Q) : boxAverage Q f x = 0 := by
  simp [boxAverage, hx]

/-- A difference is supported in its parent box. -/
theorem boxDifference_eq_zero_of_notMem (Q : Box (Fin d)) (f : (Fin d → ℝ) → ℝ)
    {x : Fin d → ℝ} (hx : x ∉ Q) : boxDifference Q f x = 0 := by
  simp only [boxDifference, Pi.sub_apply, Finset.sum_apply]
  rw [boxAverage_eq_zero_of_notMem Q f hx, sub_zero]
  apply Finset.sum_eq_zero
  intro J hJ
  exact boxAverage_eq_zero_of_notMem J f
    (fun hxJ => hx ((Prepartition.splitCenter Q).le_of_mem hJ hxJ))

theorem indicator_boxDifference (Q : Box (Fin d)) (f : (Fin d → ℝ) → ℝ) :
    (Q : Set (Fin d → ℝ)).indicator (boxDifference Q f) = boxDifference Q f := by
  funext x
  by_cases hx : x ∈ Q
  · simp [hx]
  · simp [hx, boxDifference_eq_zero_of_notMem Q f hx]

theorem measurable_boxDifference (Q : Box (Fin d)) (f : (Fin d → ℝ) → ℝ) :
    Measurable (boxDifference Q f) := by
  have hs : Measurable (fun x =>
      ∑ J ∈ (Prepartition.splitCenter Q).boxes, boxAverage J f x) :=
    (Prepartition.splitCenter Q).boxes.measurable_sum
      (fun J _ => CrossAverage.measurable_boxAverage J f)
  convert hs.sub (CrossAverage.measurable_boxAverage Q f) using 1
  ext x
  simp only [boxDifference, Pi.sub_apply, Finset.sum_apply]

theorem integrable_boxDifference (Q : Box (Fin d)) (f : (Fin d → ℝ) → ℝ) :
    Integrable (boxDifference Q f) volume := by
  exact (integrable_finsetSum' _
    (fun J _ => CrossAverage.integrable_boxAverage J f)).sub
      (CrossAverage.integrable_boxAverage Q f)

/-- On one child, the difference has the child-minus-parent average. -/
theorem boxDifference_eq_on_child {Q J : Box (Fin d)}
    (hJ : J ∈ Prepartition.splitCenter Q) (f : (Fin d → ℝ) → ℝ)
    {x : Fin d → ℝ} (hx : x ∈ J) :
    boxDifference Q f x =
      (∫ y in (J : Set (Fin d → ℝ)), f y) / volume.real (J : Set (Fin d → ℝ)) -
        (∫ y in (Q : Set (Fin d → ℝ)), f y) / volume.real (Q : Set (Fin d → ℝ)) := by
  simp only [boxDifference, Pi.sub_apply, Finset.sum_apply]
  rw [Finset.sum_eq_single J]
  · simp [boxAverage, hx, (Prepartition.splitCenter Q).le_of_mem hJ hx]
  · intro R hR hRJ
    exact boxAverage_eq_zero_of_notMem R f (fun hxR =>
      hRJ ((Prepartition.splitCenter Q).eq_of_mem_of_mem hR hJ hxR hx))
  · simp [hJ]

theorem boxDifference_constant_on_child {Q J : Box (Fin d)}
    (hJ : J ∈ Prepartition.splitCenter Q) (f : (Fin d → ℝ) → ℝ) :
    ∀ x ∈ J, ∀ y ∈ J, boxDifference Q f x = boxDifference Q f y := by
  intro x hx y hy
  rw [boxDifference_eq_on_child hJ f hx, boxDifference_eq_on_child hJ f hy]

/-- Cancellation uses local integrability and the child partition. -/
theorem integral_boxDifference (Q : Box (Fin d)) (f : (Fin d → ℝ) → ℝ)
    (hf : IntegrableOn f (Q : Set (Fin d → ℝ)) volume) :
    (∫ x, boxDifference Q f x) = 0 := by
  have hi : ∀ J ∈ (Prepartition.splitCenter Q).boxes,
      Integrable ((J : Set (Fin d → ℝ)).indicator f) volume := by
    intro J hJ
    exact (hf.mono_set ((Prepartition.splitCenter Q).le_of_mem hJ)).integrable_indicator
      J.measurableSet_coe
  have hsum : (∑ J ∈ (Prepartition.splitCenter Q).boxes,
      ∫ x in (J : Set (Fin d → ℝ)), f x) = ∫ x in (Q : Set (Fin d → ℝ)), f x := by
    calc
      _ = ∫ x, (∑ J ∈ (Prepartition.splitCenter Q).boxes,
          (J : Set (Fin d → ℝ)).indicator f) x := by
        simp only [Finset.sum_apply]
        rw [integral_finsetSum _ hi]
        exact Finset.sum_congr rfl (fun J _ => (integral_indicator J.measurableSet_coe).symm)
      _ = _ := by
        rw [sum_box_indicators _ (Prepartition.isPartition_splitCenter Q),
          integral_indicator Q.measurableSet_coe]
  change (∫ x, (∑ J ∈ (Prepartition.splitCenter Q).boxes, boxAverage J f) x -
    boxAverage Q f x) = 0
  rw [integral_sub (integrable_finsetSum' _
    (fun J _ => CrossAverage.integrable_boxAverage J f))
      (CrossAverage.integrable_boxAverage Q f)]
  simp only [Finset.sum_apply]
  rw [integral_finsetSum _ (fun J _ => CrossAverage.integrable_boxAverage J f)]
  simp_rw [CrossAverage.integral_boxAverage]
  rw [hsum, sub_self]

/-- Constancy on the whole parent forces its difference to vanish. -/
theorem boxDifference_of_constant (L : Box (Fin d)) (g : (Fin d → ℝ) → ℝ)
    (hg : ∀ x ∈ L, ∀ y ∈ L, g x = g y) : boxDifference L g = 0 := by
  have hchild : ∀ J ∈ (Prepartition.splitCenter L).boxes,
      ∀ x ∈ J, ∀ y ∈ J, g x = g y := by
    intro J hJ x hx y hy
    exact hg x ((Prepartition.splitCenter L).le_of_mem hJ hx)
      y ((Prepartition.splitCenter L).le_of_mem hJ hy)
  unfold boxDifference
  rw [sum_boxAverage_of_constant _ (Prepartition.isPartition_splitCenter L) g hchild,
    boxAverage_of_constant L g hg, sub_self]

/-- Averaging below a child preserves the restricted difference pointwise. -/
theorem boxAverage_boxDifference_of_le_child {L Q J : Box (Fin d)}
    (hJ : J ∈ Prepartition.splitCenter Q) (hLJ : L ≤ J) (f : (Fin d → ℝ) → ℝ) :
    boxAverage L (boxDifference Q f) =
      (L : Set (Fin d → ℝ)).indicator (boxDifference Q f) := by
  apply boxAverage_of_constant
  intro x hx y hy
  exact boxDifference_constant_on_child hJ f x (hLJ hx) y (hLJ hy)

/-- A containing box sees the entire cancelling integral. -/
theorem boxAverage_boxDifference_of_le {L Q : Box (Fin d)} (hQL : Q ≤ L)
    (f : (Fin d → ℝ) → ℝ) (hf : IntegrableOn f (Q : Set (Fin d → ℝ)) volume) :
    boxAverage L (boxDifference Q f) = 0 := by
  have hi : (∫ x in (L : Set (Fin d → ℝ)), boxDifference Q f x) = 0 := by
    calc
      _ = ∫ x, boxDifference Q f x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
          boxDifference_eq_zero_of_notMem Q f (fun hxQ => hx (hQL hxQ)))
      _ = 0 := integral_boxDifference Q f hf
  funext x
  simp [boxAverage, hi]

theorem boxAverage_boxDifference_of_disjoint {L Q : Box (Fin d)}
    (hLQ : Disjoint (L : Set (Fin d → ℝ)) Q) (f : (Fin d → ℝ) → ℝ) :
    boxAverage L (boxDifference Q f) = 0 := by
  have hi : (∫ x in (L : Set (Fin d → ℝ)), boxDifference Q f x) = 0 := by
    calc
      _ = ∫ _ in (L : Set (Fin d → ℝ)), (0 : ℝ) :=
        setIntegral_congr_fun L.measurableSet_coe (fun x hx =>
          boxDifference_eq_zero_of_notMem Q f (fun hxQ => Set.disjoint_left.mp hLQ hx hxQ))
      _ = 0 := by simp
  funext x
  simp [boxAverage, hi]

theorem boxDifference_boxDifference_of_le_child {L Q J : Box (Fin d)}
    (hJ : J ∈ Prepartition.splitCenter Q) (hLJ : L ≤ J) (f : (Fin d → ℝ) → ℝ) :
    boxDifference L (boxDifference Q f) = 0 := by
  apply boxDifference_of_constant
  intro x hx y hy
  exact boxDifference_constant_on_child hJ f x (hLJ hx) y (hLJ hy)

theorem boxDifference_boxDifference_of_disjoint {L Q : Box (Fin d)}
    (hLQ : Disjoint (L : Set (Fin d → ℝ)) Q) (f : (Fin d → ℝ) → ℝ) :
    boxDifference L (boxDifference Q f) = 0 := by
  change (∑ J ∈ (Prepartition.splitCenter L).boxes, boxAverage J (boxDifference Q f)) -
    boxAverage L (boxDifference Q f) = 0
  rw [boxAverage_boxDifference_of_disjoint hLQ f]
  simp only [sub_zero]
  apply Finset.sum_eq_zero
  intro J hJ
  exact boxAverage_boxDifference_of_disjoint
    (hLQ.mono_left ((Prepartition.splitCenter L).le_of_mem hJ)) f

/-- When the inner parent lies below an outer child, every outer average cancels. -/
theorem boxDifference_boxDifference_of_parent_le_child {L Q J : Box (Fin d)}
    (hJ : J ∈ Prepartition.splitCenter L) (hQJ : Q ≤ J)
    (f : (Fin d → ℝ) → ℝ) (hf : IntegrableOn f (Q : Set (Fin d → ℝ)) volume) :
    boxDifference L (boxDifference Q f) = 0 := by
  change (∑ R ∈ (Prepartition.splitCenter L).boxes, boxAverage R (boxDifference Q f)) -
    boxAverage L (boxDifference Q f) = 0
  rw [boxAverage_boxDifference_of_le
    (hQJ.trans ((Prepartition.splitCenter L).le_of_mem hJ)) f hf]
  simp only [sub_zero]
  apply Finset.sum_eq_zero
  intro R hR
  by_cases hRJ : R = J
  · subst R
    exact boxAverage_boxDifference_of_le hQJ f hf
  · exact boxAverage_boxDifference_of_disjoint
      (((Prepartition.splitCenter L).disjoint_coe_of_mem hR hJ hRJ).mono_right hQJ) f

/-- Childwise constancy reconstructs a difference, and its parent average is zero. -/
theorem boxDifference_boxDifference_self (Q : Box (Fin d)) (f : (Fin d → ℝ) → ℝ)
    (hf : IntegrableOn f (Q : Set (Fin d → ℝ)) volume) :
    boxDifference Q (boxDifference Q f) = boxDifference Q f := by
  change (∑ J ∈ (Prepartition.splitCenter Q).boxes, boxAverage J (boxDifference Q f)) -
    boxAverage Q (boxDifference Q f) = boxDifference Q f
  rw [boxAverage_boxDifference_of_le le_rfl f hf,
    sum_boxAverage_of_constant _ (Prepartition.isPartition_splitCenter Q)
      (boxDifference Q f) (fun J hJ => boxDifference_constant_on_child hJ f),
    sub_zero, indicator_boxDifference]

section Geometry

variable {ι : Type*} [Fintype ι] {I Q J L : Box ι} {n N : ℕ}

theorem mem_level_succ_of_mem_splitCenter (hQ : Q ∈ level I n)
    (hJ : J ∈ Prepartition.splitCenter Q) : J ∈ level I (n + 1) :=
  (level I n).mem_biUnion.mpr ⟨Q, hQ, hJ⟩

/-- A strict descendant lies below one and only one child. -/
theorem exists_unique_child_of_lt [Nonempty ι]
    (hL : L ∈ descendants I N) (hQ : Q ∈ descendants I N) (hLQ : L < Q) :
    ∃! J, J ∈ Prepartition.splitCenter Q ∧ L ≤ J := by
  obtain ⟨m, _, hLm⟩ := mem_descendants.mp hL
  obtain ⟨n, _, hQn⟩ := mem_descendants.mp hQ
  have hnm : n < m := by
    have hle := level_depth_le_of_le hLm hQn hLQ.le
    apply lt_of_le_of_ne hle
    intro h
    subst m
    exact hLQ.ne ((level I n).eq_of_le hLm hQn hLQ.le)
  obtain ⟨J, hJ, hLJ⟩ := level_refines I (Nat.succ_le_of_lt hnm) hLm
  obtain ⟨R, hR, hJR⟩ := (level I n).mem_biUnion.mp hJ
  have hRQ : R = Q := (level I n).eq_of_le_of_le hR hQn
    (hLJ.trans ((Prepartition.splitCenter R).le_of_mem hJR)) hLQ.le
  subst R
  refine ⟨J, ⟨hJR, hLJ⟩, ?_⟩
  intro K hK
  exact (Prepartition.splitCenter Q).eq_of_le_of_le hK.1 hJR hK.2 hLJ

end Geometry
end DifferenceAlgebra

/-- The average–difference identity on the finite grid. Strict containment gives the
nonzero case; equality gives zero by cancellation. Integrability is required only
on the top cube. Both indices may be at the smallest retained scale, where
differences use the next generation of children.

-/
theorem finite_average_difference (d : ℕ) (hd : 0 < d)
    (I : Box (Fin d)) (N : ℕ) (L Q : Box (Fin d))
    (hL : L ∈ descendants I N) (hQ : Q ∈ descendants I N)
    (f : (Fin d → ℝ) → ℝ)
    (hf : IntegrableOn f (I : Set (Fin d → ℝ)) volume) :
    boxAverage L (boxDifference Q f) =
      if L < Q then (L : Set (Fin d → ℝ)).indicator (boxDifference Q f) else 0 := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hfQ : IntegrableOn f (Q : Set (Fin d → ℝ)) volume :=
    hf.mono_set (le_of_mem_descendants hQ)
  by_cases hlt : L < Q
  · rw [ite_eq_left hlt]
    obtain ⟨J, ⟨hJ, hLJ⟩, _⟩ := DifferenceAlgebra.exists_unique_child_of_lt hL hQ hlt
    exact DifferenceAlgebra.boxAverage_boxDifference_of_le_child hJ hLJ f
  · rw [ite_eq_right hlt]
    rcases descendants_nested_or_disjoint hL hQ with hle | hle | hdis
    · have heq : L = Q := (lt_or_eq_of_le hle).resolve_left hlt
      subst L
      exact DifferenceAlgebra.boxAverage_boxDifference_of_le le_rfl f hfQ
    · exact DifferenceAlgebra.boxAverage_boxDifference_of_le hle f hfQ
    · exact DifferenceAlgebra.boxAverage_boxDifference_of_disjoint hdis f

/-- The one-coordinate orthogonality and idempotence used in `lem:cross`.

These are pointwise identities for differences of signed, locally
integrable inputs, including differences at the cutoff level.
-/
theorem finite_difference_difference (d : ℕ) (hd : 0 < d)
    (I : Box (Fin d)) (N : ℕ) (L Q : Box (Fin d))
    (hL : L ∈ descendants I N) (hQ : Q ∈ descendants I N)
    (f : (Fin d → ℝ) → ℝ)
    (hf : IntegrableOn f (I : Set (Fin d → ℝ)) volume) :
    boxDifference L (boxDifference Q f) =
      if L = Q then boxDifference Q f else 0 := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hfQ : IntegrableOn f (Q : Set (Fin d → ℝ)) volume :=
    hf.mono_set (le_of_mem_descendants hQ)
  by_cases heq : L = Q
  · subst L
    rw [ite_eq_left rfl]
    exact DifferenceAlgebra.boxDifference_boxDifference_self Q f hfQ
  · rw [ite_eq_right heq]
    rcases descendants_nested_or_disjoint hL hQ with hle | hle | hdis
    · obtain ⟨J, ⟨hJ, hLJ⟩, _⟩ :=
        DifferenceAlgebra.exists_unique_child_of_lt hL hQ (lt_of_le_of_ne hle heq)
      exact DifferenceAlgebra.boxDifference_boxDifference_of_le_child hJ hLJ f
    · obtain ⟨J, ⟨hJ, hQJ⟩, _⟩ :=
        DifferenceAlgebra.exists_unique_child_of_lt hQ hL (lt_of_le_of_ne hle (Ne.symm heq))
      exact DifferenceAlgebra.boxDifference_boxDifference_of_parent_le_child hJ hQJ f hfQ
    · exact DifferenceAlgebra.boxDifference_boxDifference_of_disjoint hdis f

end ReyZygmund.Geometry
