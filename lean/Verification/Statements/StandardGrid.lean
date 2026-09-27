import ReyZygmund.Geometry.StandardGrid

open BoxIntegral
open scoped Classical

namespace ReyZygmundVerification

open ReyZygmund.Geometry

def standardCubeMembershipContract : Prop :=
  ∀ {d : ℕ} (n : ℤ) (k : Fin d → ℤ) (x : Fin d → ℝ),
    x ∈ standardDyadicCube n k ↔
      ∀ i, ⌈x i / (2 : ℝ) ^ (-n)⌉ = k i + 1

def standardCubeInjectivityContract : Prop :=
  ∀ {d : ℕ} (n : ℤ), Function.Injective (standardDyadicCube (d := d) n)

def standardCubeChildrenContract : Prop :=
  ∀ {d : ℕ} (n : ℤ) (k : Fin d → ℤ) (s : Set (Fin d)),
    (standardDyadicCube n k).splitCenterBox s =
      standardDyadicCube (n + 1) (fun i => 2 * k i + (if i ∈ s then 1 else 0))

end ReyZygmundVerification
