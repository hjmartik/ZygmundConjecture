import ReyZygmund.Geometry.LastCoordinate

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal

namespace ReyZygmundVerification

open ReyZygmund.Geometry

def splitLastPointContract : Prop :=
  ∀ {n : ℕ} (d : Fin (n + 1) → ℕ) (x : ProductPoint d),
    splitLastCoordinates d (flattenCoordinates d x) =
      (flattenCoordinates (fun i : Fin n => d i.castSucc) (fun i => x i.castSucc),
        x (Fin.last n))

def splitLastMeasureContract : Prop :=
  ∀ {n : ℕ} (d : Fin (n + 1) → ℕ),
    MeasurePreserving (splitLastCoordinates d) volume volume

def splitLastRectangleContract : Prop :=
  ∀ {n : ℕ} (d : Fin (n + 1) → ℕ) (R : ∀ i, Box (Fin (d i)))
    (x : Fin (∑ i, d i) → ℝ),
    x ∈ flatProductBox R ↔
      splitLastCoordinates d x ∈
        ((flatProductBox (initialProjection R) :
          Set (Fin (∑ i : Fin n, d i.castSucc) → ℝ)) ×ˢ
          (R (Fin.last n) : Set (Fin (d (Fin.last n)) → ℝ)))

def splitLastIntegralContract : Prop :=
  ∀ {n : ℕ} (d : Fin (n + 1) → ℕ)
    (f : (Fin (∑ i, d i) → ℝ) → ℝ≥0∞), Measurable f →
    (∫⁻ x, f x) = ∫⁻ t, ∫⁻ y, f ((splitLastCoordinates d).symm (y, t))

end ReyZygmundVerification
