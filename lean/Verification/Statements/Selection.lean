import ReyZygmund.Selection.Shadow

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmundVerification

open ReyZygmund.Geometry ReyZygmund.Overlap

def selectedShadowComparisonContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (F G : Finset (∀ i, Box (Fin (d i)))),
      ↑F ⊆ gridRectangles D →
      (∀ Q ∈ F, (1 / 2 : ℝ) * volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ≤
        volume.real ((flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∩ finiteShadow G)) →
      volume.real (finiteShadow F) ≤ (4 : ℝ) ^ (m + 1) * volume.real (finiteShadow G)

def halfOverlapIncomparabilityContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i)))),
    (∀ Q ∈ G,
      volume.real ((flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∩ finiteShadow (G.erase Q)) ≤
        (1 / 2 : ℝ) * volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ))) →
    ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S

def finiteSelectionContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, (∀ i, 0 < d i) →
    ∀ (D : ∀ i, DyadicGrid (d i)) (F : Finset (∀ i, Box (Fin (d i)))),
      ↑F ⊆ gridRectangles D →
      ∃ G : Finset (∀ i, Box (Fin (d i))), G ⊆ F ∧
        volume.real (finiteShadow F) ≤ (4 : ℝ) ^ (m + 1) * volume.real (finiteShadow G) ∧
        (∀ Q ∈ G,
          volume.real ((flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∩ finiteShadow (G.erase Q)) ≤
            (1 / 2 : ℝ) * volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)))

end ReyZygmundVerification
