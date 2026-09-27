import ReyZygmund.Geometry.PrescribedCover

open BoxIntegral

namespace ReyZygmundVerification

open ReyZygmund.Geometry

def prescribedCoverContract : Prop :=
  ∀ {d : ℕ} (Q : Box (Fin d)) (s : ℝ), 0 < s →
    (∀ i, Q.upper i - Q.lower i = s) →
    ∃ a : Fin d → Fin 3, ∃ P : Box (Fin d),
      P ∈ (shiftedDyadicGrid d a).cubes (-roundedScale s) ∧
      Set.Icc Q.lower Q.upper ⊆ (P : Set (Fin d → ℝ)) ∧
      ∀ i, P.upper i - P.lower i = (2 : ℝ) ^ roundedScale s

def shiftedGridCardinalityContract : Prop :=
  ∀ d : ℕ, Fintype.card (Fin d → Fin 3) = 3 ^ d

end ReyZygmundVerification
