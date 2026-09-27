import ReyZygmund.Continuous.Cover

/-! Explicit propositions for the continuous cover and domination. -/

open BoxIntegral MeasureTheory
open ReyZygmund ReyZygmund.Geometry
open scoped BigOperators Classical ENNReal

namespace ReyZygmundVerification

def continuousRectangleCoverContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (R : ∀ i, Box (Fin (d i))), R ∈ continuousPhiRectangles d phi →
    ∃ (τ : ∀ i, Fin (d i) → Fin 3) (I : ∀ i, Box (Fin (d i))),
      I ∈ roundedGridRectangles (fun i => shiftedDyadicGrid (d i) (τ i)) phi ∧
      (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ⊆ flatProductBox I ∧
      volume.real (flatProductBox I : Set (Fin (∑ i, d i) → ℝ)) /
          volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤
        (8 : ℝ) ^ (∑ i, d i)

def continuousMaximalDominationContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    ∀ x : Fin (∑ i, d i) → ℝ,
      euclideanFamilyMaximal (continuousPhiRectangles d phi) f x ≤
        ENNReal.ofReal ((8 : ℝ) ^ (∑ i, d i)) *
          ⨆ τ : (∀ i, Fin (d i) → Fin 3),
            euclideanFamilyMaximal
              (roundedGridRectangles (fun i => shiftedDyadicGrid (d i) (τ i)) phi) f x

end ReyZygmundVerification
