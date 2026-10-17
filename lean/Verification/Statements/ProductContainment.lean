import ReyZygmund.Geometry.ProductContainment

open BoxIntegral

namespace ReyZygmundVerification

open ReyZygmund.Geometry

def productRectangleContainmentContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (Q R : ∀ i, Box (Fin (d i))),
    productRectangle Q ⊆ productRectangle R ↔ ∀ i, Q i ≤ R i

def productRectangleInjectivityContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}, Function.Injective (productRectangle (d := d))

end ReyZygmundVerification
