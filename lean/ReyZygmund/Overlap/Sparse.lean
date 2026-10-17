import ReyZygmund.MathlibOnly.Definitions

/-! # Borel subsets establishing sparseness

The Lebesgue-measurable subsets in `Sparse` can be replaced by Borel subsets with
the same sparsity parameter.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.MathlibOnly

variable {m : ℕ} {d : Fin m → ℕ}

/-- Shrinking each set establishing sparseness to a Borel subset preserves
the sparsity parameter. -/
theorem sparse_iff_exists_measurable (eta : ℝ) (G : Set (Rectangle d)) :
    Sparse eta G ↔
      ∃ E : Rectangle d → Set (Point d),
        (∀ R ∈ G, MeasurableSet (E R) ∧ E R ⊆ rectangle R ∧
          ENNReal.ofReal eta * volume (rectangle R) ≤ volume (E R)) ∧
        G.Pairwise (fun R S => Disjoint (E R) (E S)) := by
  constructor
  · rintro ⟨E, hE, hdis⟩
    let B := fun R => (toMeasurable volume (E R)ᶜ)ᶜ
    have hsub (R) : B R ⊆ E R :=
      Set.compl_subset_comm.mp (subset_toMeasurable volume (E R)ᶜ)
    refine ⟨B, ?_, ?_⟩
    · intro R hR
      refine ⟨(measurableSet_toMeasurable _ _).compl, (hsub R).trans (hE R hR).2.1, ?_⟩
      rw [show volume (B R) = volume (E R) from
        measure_congr (hE R hR).1.compl_toMeasurable_compl_ae_eq]
      exact (hE R hR).2.2
    · intro R hR S hS hne
      exact (hdis hR hS hne).mono (hsub R) (hsub S)
  · rintro ⟨E, hE, hdis⟩
    exact ⟨E, fun R hR => ⟨(hE R hR).1.nullMeasurableSet, (hE R hR).2⟩, hdis⟩

end ReyZygmund.MathlibOnly
