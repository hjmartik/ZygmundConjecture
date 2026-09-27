import ReyZygmund.Overlap.Pairing

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry ReyZygmund.Overlap

def finiteSparsePairingContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (G : Finset (∀ i, Box (Fin (d i)))) (eta : ℝ), 0 < eta →
  ∀ (E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ)),
    (∀ R ∈ G, MeasurableSet (E R)) →
    (∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) →
    Set.Pairwise (G : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (E R) (E S)) →
    (∀ R ∈ G,
      ENNReal.ofReal eta * volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤
        volume (E R)) →
  ∀ (g : (Fin (∑ i, d i) → ℝ) → ℝ),
    (∀ x ∈ finiteShadow G, 0 ≤ g x) →
    (∀ R ∈ G, IntegrableOn g (flatProductBox R) volume) →
      eta * (∫ x, finiteOverlap G x * g x) ≤
        ∫ x in finiteShadow G, (euclideanFamilyMaximal (G : Set _) g x).toReal

end ReyZygmundVerification
