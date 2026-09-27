import ReyZygmund.Geometry.GlobalDifferences

/-! Statements about finite difference expansions and their integrability. Only the
underlying definitions are imported, not the proofs. These are supporting facts
for the full-grid maximal–square estimate.
-/

open BoxIntegral MeasureTheory ReyZygmund.Geometry
open scoped BigOperators Classical

namespace ReyZygmundVerification

noncomputable def rawProductDifferenceMeasurableContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (Q : ∀ i, Box (Fin (d i)))
    (g : ProductPoint d → ℝ),
    Measurable (rawProductDifference Q g)

noncomputable def rawProductDifferenceBoundedContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (Q : ∀ i, Box (Fin (d i)))
    (g : ProductPoint d → ℝ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |rawProductDifference Q g x| ≤ C

noncomputable def rawProductDifferenceIntegrableContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (Q : ∀ i, Box (Fin (d i)))
    (g : ProductPoint d → ℝ),
    Integrable (rawProductDifference Q g) volume

noncomputable def rawProductDifferenceAEInvariantContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (Q : ∀ i, Box (Fin (d i)))
    {g h : ProductPoint d → ℝ},
    (g =ᵐ[volume] h) → rawProductDifference Q g = rawProductDifference Q h

noncomputable def finiteRawExpansionIntegrableContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (H : Finset (∀ i, Box (Fin (d i)))) (g : ProductPoint d → ℝ),
    (g =ᵐ[volume] fun x => ∑ Q ∈ H, rawProductDifference Q g x) →
    Integrable g volume

noncomputable def finiteRawExpansionRepresentativeContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (H : Finset (∀ i, Box (Fin (d i)))) (g : ProductPoint d → ℝ),
    (g =ᵐ[volume] fun x => ∑ Q ∈ H, rawProductDifference Q g x) →
    ∃ F : boundedMeasurableFunctions d,
      (g =ᵐ[volume] F.1) ∧ Integrable F.1 volume ∧
      (∀ Q, rawProductDifference Q g = rawProductDifference Q F.1) ∧
      (F.1 = fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x)

end ReyZygmundVerification
