import ReyZygmund.Geometry.GlobalDifferences

/-! Statement equating the rectangle-integral formula with the product of coordinate
differences. The proof module is not imported. -/

open BoxIntegral ReyZygmund.Geometry
open scoped Classical

namespace ReyZygmundVerification

noncomputable def rawProductDifferenceCoordinateContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (Q : ∀ i, Box (Fin (d i)))
    (F : boundedMeasurableFunctions d),
    rawProductDifference Q F.1 = (productDifferenceMap Finset.univ Q F).1

end ReyZygmundVerification
