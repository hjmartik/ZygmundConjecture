import ReyZygmund.Geometry.ProductSteps
import ReyZygmund.Geometry.FiniteCrossAverage

/-!
Expected propositions for the finite analytic ingredients. These statements use
the separately reviewed concrete definitions, not candidate theorem types.
Their limited scope does not include the common product projection or global grids.
-/

open BoxIntegral MeasureTheory ReyZygmund.Geometry
open scoped BigOperators Classical

namespace ReyZygmundVerification

noncomputable def productStepRepresentationContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ), ProductLeafConstant I N f →
    (productBox I).indicator f =
      ∑ Q ∈ productLeaves I N,
        (productBox Q).indicator (fun _ => f (fun i => (Q i).upper))

noncomputable def productStepMeasurabilityContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ), ProductLeafConstant I N f →
    Measurable ((productBox I).indicator f)

noncomputable def productStepBoundednessContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ), ProductLeafConstant I N f →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |(productBox I).indicator f x| ≤ C

noncomputable def coordinateAverageMeasurabilityContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (i : Fin m) (Q : Box (Fin (d i)))
    (f : ProductPoint d → ℝ), Measurable f → Measurable (coordinateAverage i Q f)

noncomputable def finiteCoordinateCommutationContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ), ProductLeafConstant I N f →
    ∀ (i j : Fin m), i ≠ j → ∀ (Q : Box (Fin (d i))) (R : Box (Fin (d j))),
    coordinateAverage i Q (coordinateAverage j R ((productBox I).indicator f)) =
      coordinateAverage j R (coordinateAverage i Q ((productBox I).indicator f))

noncomputable def finiteCrossAverageContract : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (I : Box (Fin d)) (N : ℕ)
    (eligible : Finset (Box (Fin d))), eligible ⊆ descendants I N →
    ∀ (g : (Fin d → ℝ) → ℝ),
    (∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y) →
    IntegrableOn g (I : Set (Fin d → ℝ)) volume ∧
      Measurable (finiteCrossAverage I N eligible g) ∧
      Integrable (finiteCrossAverage I N eligible g) volume ∧
      (∫ x, finiteCrossAverage I N eligible g x) =
        (∫ x in (I : Set (Fin d → ℝ)), g x) ∧
      (I : Set (Fin d → ℝ)).indicator g - finiteCrossAverage I N eligible g =
        ∑ L ∈ (interior I N).filter (fun L => ∃ J ∈ eligible, L ≤ J), boxDifference L g

noncomputable def crossAverageSupportContract : Prop :=
  ∀ {d : ℕ} {I : Box (Fin d)} {N : ℕ} {eligible : Finset (Box (Fin d))},
    eligible ⊆ descendants I N → ∀ (g : (Fin d → ℝ) → ℝ) {x : Fin d → ℝ},
    x ∉ I → finiteCrossAverage I N eligible g x = 0

noncomputable def crossAverageLeafConstancyContract : Prop :=
  ∀ {d : ℕ} {I : Box (Fin d)} {N : ℕ} {eligible : Finset (Box (Fin d))},
    eligible ⊆ descendants I N → ∀ (g : (Fin d → ℝ) → ℝ),
    ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q,
      finiteCrossAverage I N eligible g x = finiteCrossAverage I N eligible g y

end ReyZygmundVerification
