import ReyZygmund.Continuous.StrictCover

/-! Explicit strict-cover proposition with its necessary dimension guard. -/

open BoxIntegral MeasureTheory ReyZygmund.Geometry
open scoped BigOperators Classical ENNReal

namespace ReyZygmundVerification

def continuousStrictCoverContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}, 0 < ∑ i, d i →
  ∀ (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (R : ∀ i, Box (Fin (d i))), R ∈ continuousPhiRectangles d phi →
    ∃ (tau : ∀ i, Fin (d i) → Fin 3) (I : ∀ i, Box (Fin (d i))),
      I ∈ roundedGridRectangles (fun i => shiftedDyadicGrid (d i) (tau i)) phi ∧
      (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ⊆ flatProductBox I ∧
      volume.real (flatProductBox I : Set (Fin (∑ i, d i) → ℝ)) /
          volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) <
        (8 : ℝ) ^ (∑ i, d i)

end ReyZygmundVerification
