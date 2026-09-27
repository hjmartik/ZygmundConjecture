import ReyZygmund.Geometry.ProductContainment

open BoxIntegral

namespace ReyZygmundVerification

open ReyZygmund.Geometry

def productBoxContainmentContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (Q R : ∀ i, Box (Fin (d i))),
    productBox Q ⊆ productBox R ↔ ∀ i, Q i ≤ R i

def productBoxInjectivityContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, Function.Injective (productBox (d := d))

end ReyZygmundVerification
