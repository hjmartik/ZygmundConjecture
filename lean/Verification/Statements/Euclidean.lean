import ReyZygmund.Maximal.Euclidean

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry

def euclideanMaximalFlattenContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (x : ProductPoint d),
    euclideanFamilyMaximal G f (flattenCoordinates d x) =
      familyMaximal G (fun y => f (flattenCoordinates d y)) x

def euclideanMaximalMeasurableContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i)))),
    G.Countable → ∀ f : (Fin (∑ i, d i) → ℝ) → ℝ,
      Measurable (euclideanFamilyMaximal G f)

def euclideanMaximalFiniteAEContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m → (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (G : Set (∀ i, Box (Fin (d i)))),
    G ⊆ gridRectangles D →
    (∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → R = S) →
    ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ), 1 < p →
    MemLp f (ENNReal.ofReal p) volume →
      ∀ᵐ x ∂volume, euclideanFamilyMaximal G f x < ∞

def euclideanMaximalNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, 2 ≤ m → (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (G : Set (∀ i, Box (Fin (d i)))),
    G ⊆ gridRectangles D →
    (∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → R = S) →
    ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ), 1 < p →
    MemLp f (ENNReal.ofReal p) volume →
    eLpNorm (fun x => (euclideanFamilyMaximal G f x).toReal) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1)) * eLpNorm f (ENNReal.ofReal p) volume

end ReyZygmundVerification
