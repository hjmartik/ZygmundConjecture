import Mathlib.Analysis.BoxIntegral.Partition.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Integrability on a finite box partition

A function constant on every member of a finite box partition is integrable
on the whole box.
-/

open MeasureTheory

namespace BoxIntegral.Prepartition

theorem IsPartition.integrableOn_of_constant
    {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Box ι} {π : Prepartition I} (hπ : π.IsPartition)
    (g : (ι → ℝ) → E)
    (hg : ∀ Q ∈ π.boxes, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y) :
    IntegrableOn g (I : Set (ι → ℝ)) volume := by
  rw [← hπ.iUnion_eq, Prepartition.iUnion_def]
  apply integrableOn_finset_iUnion.mpr
  intro Q hQ
  have hc : IntegrableOn (fun _ : ι → ℝ => g Q.upper)
      (Q : Set (ι → ℝ)) volume :=
    integrableOn_const (Q.measure_coe_lt_top volume).ne
  exact hc.congr_fun (fun x hx => hg Q hQ Q.upper Q.upper_mem x hx) Q.measurableSet_coe

end BoxIntegral.Prepartition
