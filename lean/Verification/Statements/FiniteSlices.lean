import ReyZygmund.Geometry.FiniteSlices

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmundVerification

open ReyZygmund.Geometry ReyZygmund.Overlap

def finiteSlicedOverlapContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (D : ∀ i, DyadicGrid (d i)) (G : Finset (∀ i, Box (Fin (d i)))),
    (↑G : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D →
    (∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S) →
    ∀ (y : Fin (∑ i : Fin n, d i.castSucc) → ℝ) (t : Fin (d (Fin.last n)) → ℝ),
      finiteOverlap G ((splitLastCoordinates d).symm (y, t)) =
        finiteOverlap (finiteSlice G t) y

def finiteSlicedShadowContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ} (G : Finset (∀ i, Box (Fin (d i))))
    (y : Fin (∑ i : Fin n, d i.castSucc) → ℝ) (t : Fin (d (Fin.last n)) → ℝ),
    (splitLastCoordinates d).symm (y, t) ∈ finiteShadow G ↔
      y ∈ finiteShadow (finiteSlice G t)

def finiteSlicedShadowMeasureContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ} (G : Finset (∀ i, Box (Fin (d i)))),
    volume (finiteShadow G) = ∫⁻ t, volume (finiteShadow (finiteSlice G t))

end ReyZygmundVerification
