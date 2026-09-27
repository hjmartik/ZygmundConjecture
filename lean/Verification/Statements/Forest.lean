import ReyZygmund.Maximal.Forest

open BoxIntegral MeasureTheory
open scoped Classical BigOperators

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry

def finiteMaximalPowerIntegrableContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i))))
    (f : ProductPoint d → ℝ) (p : ℝ), 0 < p →
    Integrable (fun x => Real.rpow (finiteFunctionMaximal G f x) p) volume

def finiteMaximalForestContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (T G : Finset (∀ i, Box (Fin (d i)))),
  Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
    (fun R S => Disjoint (productBox R) (productBox S)) →
  (∀ Q ∈ G, ∃ R ∈ T, ∀ i, Q i ≤ R i) →
  ∀ (f : ProductPoint d → ℝ) (x : ProductPoint d),
    finiteFunctionMaximal G f x =
      ∑ R ∈ T, finiteFunctionMaximal
        (G.filter (fun Q => ∀ i, Q i ≤ R i)) f x

def finiteMaximalForestIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (T G : Finset (∀ i, Box (Fin (d i)))),
  Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
    (fun R S => Disjoint (productBox R) (productBox S)) →
  (∀ Q ∈ G, ∃ R ∈ T, ∀ i, Q i ≤ R i) →
  ∀ (f : ProductPoint d → ℝ) (p : ℝ), 0 < p →
    (∫ x, Real.rpow (finiteFunctionMaximal G f x) p) =
      ∑ R ∈ T, ∫ x in productBox R,
        Real.rpow (finiteFunctionMaximal
          (G.filter (fun Q => ∀ i, Q i ≤ R i)) f x) p

end ReyZygmundVerification
