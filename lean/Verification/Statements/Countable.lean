import ReyZygmund.Maximal.Countable

open BoxIntegral MeasureTheory
open scoped Classical ENNReal

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry

def countableFamilyMaximalMeasurableContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i)))),
    G.Countable → ∀ f : ProductPoint d → ℝ, Measurable (familyMaximal G f)

def familyMaximalFiniteSupContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i))))
    (f : ProductPoint d → ℝ) (x : ProductPoint d),
    familyMaximal G f x = ⨆ H : Finset G,
      ENNReal.ofReal (finiteFunctionMaximal (H.image Subtype.val) f x)

def familyMaximalIntegralSupContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i)))),
  G.Countable → ∀ (f : ProductPoint d → ℝ) (p : ℝ), 0 < p →
    (∫⁻ x, (familyMaximal G f x) ^ p) =
      ⨆ H : Finset G, ∫⁻ x,
        (ENNReal.ofReal (finiteFunctionMaximal (H.image Subtype.val) f x)) ^ p

def familyMaximalIntegralBoundContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i)))),
  G.Countable → ∀ (f : ProductPoint d → ℝ) (p : ℝ), 0 < p →
  ∀ C : ℝ≥0∞, (∀ H : Finset G, (∫⁻ x,
    (ENNReal.ofReal (finiteFunctionMaximal (H.image Subtype.val) f x)) ^ p) ≤ C) →
    (∫⁻ x, (familyMaximal G f x) ^ p) ≤ C

end ReyZygmundVerification
