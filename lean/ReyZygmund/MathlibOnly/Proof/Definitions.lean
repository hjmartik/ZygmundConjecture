import ReyZygmund.MathlibOnly.Definitions

/-! # Conditions used in the overlap proofs

The rectangle families, maximal functions and sparsity condition are those of
the independent specification. Containment leaving one factor unchanged is an
equivalent form of weak incomparability used in the proofs.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.MathlibOnly.Proof

/-- Containment leaves at least one entire cube factor unchanged. -/
def HasEqualFactorOnContainment {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i)))) : Prop :=
  ∀ R ∈ G, ∀ S ∈ G, rectangle R ⊆ rectangle S → ∃ i, R i = S i

end ReyZygmund.MathlibOnly.Proof
