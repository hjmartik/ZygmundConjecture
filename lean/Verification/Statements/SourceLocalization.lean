import ReyZygmund.Maximal.GeneralInput

/-! Localization with inputs restricted to the top rectangles. The power identity uses
global integrals on both sides. The localization proof is not imported.
-/

open BoxIntegral MeasureTheory
open scoped Classical BigOperators

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry

def sourceLocalMaximalIndicatorContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (H : Finset (∀ i, Box (Fin (d i))))
    (R : ∀ i, Box (Fin (d i))),
    (∀ Q ∈ H, productBox Q ⊆ productBox R) → ∀ f : ProductPoint d → ℝ,
      finiteFunctionMaximal H ((productBox R).indicator f) =
        finiteFunctionMaximal H f

def sourceForestLocalizationContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (T G : Finset (∀ i, Box (Fin (d i)))),
    Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (productBox R) (productBox S)) →
    (∀ Q ∈ G, ∃ R ∈ T, ∀ i, Q i ≤ R i) →
    ∀ (f : ProductPoint d → ℝ) (x : ProductPoint d),
      finiteFunctionMaximal G f x =
        ∑ R ∈ T, finiteFunctionMaximal
          (G.filter (fun Q => ∀ i, Q i ≤ R i)) ((productBox R).indicator f) x

def sourceForestPowerIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (T G : Finset (∀ i, Box (Fin (d i)))),
    Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (productBox R) (productBox S)) →
    (∀ Q ∈ G, ∃ R ∈ T, ∀ i, Q i ≤ R i) →
    ∀ (f : ProductPoint d → ℝ) (p : ℝ), 0 < p →
      (∫ x, Real.rpow (finiteFunctionMaximal G f x) p) =
        ∑ R ∈ T, ∫ x, Real.rpow (finiteFunctionMaximal
          (G.filter (fun Q => ∀ i, Q i ≤ R i)) ((productBox R).indicator f) x) p

end ReyZygmundVerification
