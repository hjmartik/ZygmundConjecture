import ReyZygmund.Geometry.GlobalDifferences
import ReyZygmund.Geometry.ProductClosure

/-! Statements of the finite step-function identities, written from the
child-minus-parent formula and the partitions into smallest cubes. Neither
regularity nor constancy of the original input is assumed. -/

open BoxIntegral
open scoped Classical

namespace ReyZygmundVerification

open ReyZygmund.Geometry ReyZygmund.Projection

def descendantIndicatorLeafConstantContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (P : ∀ i, Box (Fin (d i))),
    P ∈ productDescendants I N → ∀ c : ℝ,
      ProductLeafConstant I N ((productBox P).indicator (fun _ => c))

def differenceRectanglesContainmentContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (A : Finset (Fin m))
    (Q R : ∀ i, Box (Fin (d i))),
    R ∈ differenceRectangles A Q → ∀ i, R i ≤ Q i

def differenceRectanglesDescendantContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A : Finset (Fin m)) (Q R : ∀ i, Box (Fin (d i))),
    Q ∈ productInterior I N → R ∈ differenceRectangles A Q →
      R ∈ productDescendants I N

def rawDifferenceLeafConstantContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (Q : ∀ i, Box (Fin (d i))),
    Q ∈ productInterior I N → ∀ g : ProductPoint d → ℝ,
      ProductLeafConstant I N (rawProductDifference Q g)

def rawDifferenceSupportContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (Q : ∀ i, Box (Fin (d i))) (g : ProductPoint d → ℝ)
    (x : ProductPoint d),
    x ∉ productBox Q → rawProductDifference Q g x = 0

end ReyZygmundVerification
