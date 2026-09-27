import ReyZygmund.Maximal.WeakerGlobal

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry

def weakerGlobalMaximalIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m → (∀ i, 0 < d i) →
  ∀ (D : ∀ i, DyadicGrid (d i)) (G : Set (∀ i, Box (Fin (d i)))),
  G ⊆ gridRectangles D →
  (∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → ∃ i, R i = S i) →
  ∀ (f : ProductPoint d → ℝ) (p : ℝ), 1 < p →
  MemLp f (ENNReal.ofReal p) volume →
    (∫⁻ x, (familyMaximal G f x) ^ p) ≤
      (ENNReal.ofReal ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1))) ^ p *
          ∫⁻ x, (ENNReal.ofReal |f x|) ^ p

def weakerGlobalMaximalFiniteAEContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m → (∀ i, 0 < d i) →
  ∀ (D : ∀ i, DyadicGrid (d i)) (G : Set (∀ i, Box (Fin (d i)))),
  G ⊆ gridRectangles D →
  (∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → ∃ i, R i = S i) →
  ∀ (f : ProductPoint d → ℝ) (p : ℝ), 1 < p →
  MemLp f (ENNReal.ofReal p) volume →
    ∀ᵐ x ∂volume, familyMaximal G f x < ∞

def weakerGlobalMaximalNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m → (∀ i, 0 < d i) →
  ∀ (D : ∀ i, DyadicGrid (d i)) (G : Set (∀ i, Box (Fin (d i)))),
  G ⊆ gridRectangles D →
  (∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → ∃ i, R i = S i) →
  ∀ (f : ProductPoint d → ℝ) (p : ℝ), 1 < p →
  MemLp f (ENNReal.ofReal p) volume →
    eLpNorm (fun x => (familyMaximal G f x).toReal) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1)) * eLpNorm f (ENNReal.ofReal p) volume

def weakerGlobalSetContainmentNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m → (∀ i, 0 < d i) →
  ∀ (D : ∀ i, DyadicGrid (d i)) (G : Set (∀ i, Box (Fin (d i)))),
  G ⊆ gridRectangles D →
  (∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i) →
  ∀ (f : ProductPoint d → ℝ) (p : ℝ), 1 < p →
  MemLp f (ENNReal.ofReal p) volume →
    eLpNorm (fun x => (familyMaximal G f x).toReal) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1)) * eLpNorm f (ENNReal.ofReal p) volume

def euclideanWeakerMaximalFiniteAEContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m → (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (G : Set (∀ i, Box (Fin (d i)))),
    G ⊆ gridRectangles D →
    (∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i) →
    ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ), 1 < p →
    MemLp f (ENNReal.ofReal p) volume →
      ∀ᵐ x ∂volume, euclideanFamilyMaximal G f x < ∞

def euclideanWeakerMaximalNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m → (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (G : Set (∀ i, Box (Fin (d i)))),
    G ⊆ gridRectangles D →
    (∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i) →
    ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ), 1 < p →
    MemLp f (ENNReal.ofReal p) volume →
    eLpNorm (fun x => (euclideanFamilyMaximal G f x).toReal) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1)) * eLpNorm f (ENNReal.ofReal p) volume

end ReyZygmundVerification

