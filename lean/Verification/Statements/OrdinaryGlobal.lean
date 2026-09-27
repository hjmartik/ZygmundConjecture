import ReyZygmund.Maximal.OrdinaryGlobal

/-! Explicit expected propositions for the all-p ordinary product-grid bound. -/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry

def ordinaryFiniteGridIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (G : Finset (∀ i, Box (Fin (d i)))),
    ↑G ⊆ gridRectangles D →
    ∀ (f : ProductPoint d → ℝ) (p : ℝ), 1 < p →
    MemLp f (ENNReal.ofReal p) volume →
      (∫ x, Real.rpow (finiteFunctionMaximal G f x) p) ≤
        Real.rpow (p / (p - 1)) (p * (m : ℝ)) * ∫ x, Real.rpow |f x| p

def ordinaryFiniteGridLIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (G : Finset (∀ i, Box (Fin (d i)))),
    ↑G ⊆ gridRectangles D →
    ∀ (f : ProductPoint d → ℝ) (p : ℝ), 1 < p →
    MemLp f (ENNReal.ofReal p) volume →
      (∫⁻ x, (ENNReal.ofReal (finiteFunctionMaximal G f x)) ^ p) ≤
        (ENNReal.ofReal ((p / (p - 1)) ^ m)) ^ p *
          ∫⁻ x, (ENNReal.ofReal |f x|) ^ p

def ordinaryGlobalLIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (G : Set (∀ i, Box (Fin (d i)))),
    G ⊆ gridRectangles D →
    ∀ (f : ProductPoint d → ℝ) (p : ℝ), 1 < p →
    MemLp f (ENNReal.ofReal p) volume →
      (∫⁻ x, (familyMaximal G f x) ^ p) ≤
        (ENNReal.ofReal ((p / (p - 1)) ^ m)) ^ p *
          ∫⁻ x, (ENNReal.ofReal |f x|) ^ p

def ordinaryGlobalFiniteAEContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (G : Set (∀ i, Box (Fin (d i)))),
    G ⊆ gridRectangles D →
    ∀ (f : ProductPoint d → ℝ) (p : ℝ), 1 < p →
    MemLp f (ENNReal.ofReal p) volume →
      ∀ᵐ x ∂volume, familyMaximal G f x < ∞

def ordinaryGlobalNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (G : Set (∀ i, Box (Fin (d i)))),
    G ⊆ gridRectangles D →
    ∀ (f : ProductPoint d → ℝ) (p : ℝ), 1 < p →
    MemLp f (ENNReal.ofReal p) volume →
      eLpNorm (fun x => (familyMaximal G f x).toReal) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal ((p / (p - 1)) ^ m) * eLpNorm f (ENNReal.ofReal p) volume

def ordinaryEuclideanFiniteAEContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (G : Set (∀ i, Box (Fin (d i)))),
    G ⊆ gridRectangles D →
    ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ), 1 < p →
    MemLp f (ENNReal.ofReal p) volume →
      ∀ᵐ x ∂volume, euclideanFamilyMaximal G f x < ∞

def ordinaryEuclideanNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (G : Set (∀ i, Box (Fin (d i)))),
    G ⊆ gridRectangles D →
    ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ), 1 < p →
    MemLp f (ENNReal.ofReal p) volume →
      eLpNorm (fun x => (euclideanFamilyMaximal G f x).toReal) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal ((p / (p - 1)) ^ m) * eLpNorm f (ENNReal.ofReal p) volume

end ReyZygmundVerification
