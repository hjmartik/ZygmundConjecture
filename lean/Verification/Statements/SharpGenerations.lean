import ReyZygmund.Sharpness.Generations

/-! Statements of the generation identities for the sharpness construction. -/

open scoped BigOperators

namespace ReyZygmundVerification

open ReyZygmund.Sharpness

def sharpGenerationNonnegContract : Prop :=
  ∀ {n N : ℕ}, 2 ≤ N → ∀ (s : ℕ) (a : Fin (n + 2) → Fin N)
    (i : Fin (n + 3)), 0 ≤ sharpGeneration s a i

def sharpGenerationSumContract : Prop :=
  ∀ {n N : ℕ} (s : ℕ) (a : Fin (n + 2) → Fin N),
    sharpGeneration s a (Fin.last (n + 2)) =
      ∑ i : Fin (n + 2), sharpGeneration s a i.castSucc

def sharpGenerationDominationContract : Prop :=
  ∀ {n N s : ℕ}, 2 ≤ N → 1 ≤ s → ∀ (a a' : Fin (n + 2) → Fin N),
    (∀ i, sharpGeneration s a' i ≤ sharpGeneration s a i) → a = a'

def selectionScaleOneContract : Prop :=
  ∀ {n N : ℕ}, 2 ≤ N → ∀ i : Fin (n + 2), 1 ≤ selectionScale N i 1

def selectionScaleStepContract : Prop :=
  ∀ {n N : ℕ}, 2 ≤ N → ∀ (i : Fin (n + 2)) (k : ℕ),
    selectionScale N i k ≤ selectionScale N i (k + 1) - 1

def sharpGenerationSelectionScaledContract : Prop :=
  ∀ {n N : ℕ} (s : ℕ) (a : Fin (n + 2) → Fin N) (i : Fin (n + 2)),
    (s : ℤ) * selectionScale N i (a i).val ≤ sharpGeneration s a i.succ ∧
      sharpGeneration s a i.succ ≤
        (s : ℤ) * (selectionScale N i ((a i).val + 1) - 1)

def sharpGenerationSelectionContract : Prop :=
  ∀ {n N s : ℕ}, 1 ≤ s → ∀ (a : Fin (n + 2) → Fin N) (i : Fin (n + 2)),
    selectionScale N i (a i).val ≤ sharpGeneration s a i.succ / (s : ℤ) ∧
      sharpGeneration s a i.succ / (s : ℤ) ≤
        selectionScale N i ((a i).val + 1) - 1

def sharpGenerationSelectionEqContract : Prop :=
  ∀ {n N s : ℕ}, 1 ≤ s → ∀ (a : Fin (n + 2) → Fin N) (i : Fin (n + 2)), i ≠ 0 →
    selectionScale N i (a i).val = sharpGeneration s a i.succ / (s : ℤ) ∧
      sharpGeneration s a i.succ / (s : ℤ) =
        selectionScale N i ((a i).val + 1) - 1

end ReyZygmundVerification
