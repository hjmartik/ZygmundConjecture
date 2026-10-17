import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Integration over null-measurable sets

A constant lower bound can be integrated over a null-measurable set, and an
integral over a finite almost-everywhere disjoint union splits into a sum.
-/

open Function Set
open scoped BigOperators ENNReal

namespace MeasureTheory

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} {f : X → E}

/-- The integral over a finite union of null-measurable, almost-everywhere
pairwise disjoint sets is the sum of the integrals. -/
theorem integral_biUnion_finset₀ {ι : Type*} (t : Finset ι) {s : ι → Set X}
    (hs : ∀ i ∈ t, NullMeasurableSet (s i) μ)
    (h's : Set.Pairwise (↑t) (AEDisjoint μ on s))
    (hf : ∀ i ∈ t, IntegrableOn f (s i) μ) :
    ∫ x in ⋃ i ∈ t, s i, f x ∂μ = ∑ i ∈ t, ∫ x in s i, f x ∂μ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t hat IH =>
    simp only [Finset.coe_insert, Finset.forall_mem_insert, Set.pairwise_insert,
      Finset.set_biUnion_insert] at hs hf h's ⊢
    rw [setIntegral_union₀ _ _ hf.1 (integrableOn_finset_iUnion.2 hf.2)]
    · rw [Finset.sum_insert hat, IH hs.2 h's.1 hf.2]
    · simp only [AEDisjoint, inter_iUnion]
      exact (measure_biUnion_null_iff t.countable_toSet).2 fun i hi =>
        (h's.2 i hi (ne_of_mem_of_not_mem hi hat).symm).1
    · exact t.nullMeasurableSet_biUnion hs.2

variable [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
  [ClosedIciTopology E] [CompleteSpace E] {s : Set X}

/-- Integrating a constant lower bound on a null-measurable set of finite measure. -/
theorem setIntegral_ge_of_const_le₀ {c : E} (hs : NullMeasurableSet s μ)
    (hμs : μ s ≠ ∞) (hf : ∀ x ∈ s, c ≤ f x) (hfint : IntegrableOn f s μ) :
    μ.real s • c ≤ ∫ x in s, f x ∂μ := by
  rw [← setIntegral_const c]
  exact setIntegral_mono_on₀ (integrableOn_const hμs) hfint hs hf

end MeasureTheory
