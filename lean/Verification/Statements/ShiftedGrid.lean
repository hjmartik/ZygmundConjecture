import ReyZygmund.Geometry.ShiftedGrid

/-! Explicit propositions for the alternating shifted cubes. -/

open BoxIntegral
open scoped Classical

namespace ReyZygmundVerification

open ReyZygmund.Geometry

def shiftedCubeMembershipContract : Prop :=
  ∀ {d : ℕ} (a : Fin d → Fin 3) (n : ℤ)
    (z : Fin d → ℤ) (x : Fin d → ℝ),
    x ∈ shiftedDyadicCube a n z ↔
      ∀ i, ⌈x i / (2 : ℝ) ^ (-n) - (-1 : ℝ) ^ n * ((a i).val : ℝ) / 3⌉ =
        z i + 1

def shiftedCubeInjectivityContract : Prop :=
  ∀ {d : ℕ} (a : Fin d → Fin 3) (n : ℤ),
    Function.Injective (shiftedDyadicCube a n)

def shiftedCubeChildrenContract : Prop :=
  ∀ {d : ℕ} (a : Fin d → Fin 3) (n : ℤ) (z : Fin d → ℤ) (s : Set (Fin d)),
    (shiftedDyadicCube a n z).splitCenterBox s =
      shiftedDyadicCube a (n + 1) (fun i =>
        2 * z i + (if Even n then 1 else -1) * ((a i).val : ℤ) +
          (if i ∈ s then 1 else 0))

end ReyZygmundVerification
