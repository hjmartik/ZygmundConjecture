import ReyZygmund.Continuous.Endpoint

/-! Explicit helper propositions for the continuous endpoint transfer. -/

open BoxIntegral MeasureTheory ReyZygmund ReyZygmund.Geometry
open scoped BigOperators Classical ENNReal

namespace ReyZygmundVerification

def logDilationContract : Prop :=
  ∀ {A u : ℝ}, 1 ≤ A → 0 ≤ u →
    Real.log (Real.exp 1 + A * u) ≤
      (1 + Real.log A) * Real.log (Real.exp 1 + u)

def orliczDilationContract : Prop :=
  ∀ (q : ℕ) {A u : ℝ}, 1 ≤ A → 0 ≤ u →
    (A * u) * (Real.log (Real.exp 1 + A * u)) ^ q ≤
      (A * (1 + Real.log A) ^ q) *
        (u * (Real.log (Real.exp 1 + u)) ^ q)

def prescribedShiftCountContract : Prop :=
  ∀ {m : ℕ} (d : Fin m → ℕ),
    Fintype.card (∀ i, Fin (d i) → Fin 3) = 3 ^ (∑ i, d i)

def continuousLevelsetInclusionContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    ∀ (lam : ℝ), 0 < lam →
    {x | ENNReal.ofReal lam < euclideanFamilyMaximal (continuousPhiRectangles d phi) f x} ⊆
      ⋃ tau : (∀ i, Fin (d i) → Fin 3),
        {x | ENNReal.ofReal (lam / (8 : ℝ) ^ (∑ i, d i)) <
          euclideanFamilyMaximal
            (roundedGridRectangles (fun i => shiftedDyadicGrid (d i) (tau i)) phi) f x}

end ReyZygmundVerification
