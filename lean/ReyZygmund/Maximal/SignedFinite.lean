import ReyZygmund.Geometry.GlobalDifferences

/-! The finite supremum of absolute values of signed rectangle averages. The empty
family has value zero; the absolute value is outside each integral.
-/

open BoxIntegral MeasureTheory
open scoped ENNReal Classical

namespace ReyZygmund

open Geometry

noncomputable def finiteSignedGridMaximal {m : ℕ} {d : Fin m → ℕ}
    (H : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ)
    (x : ProductPoint d) : ℝ≥0∞ :=
  H.sup (fun Q => ENNReal.ofReal ((productBox Q).indicator
    (fun _ => |(∫ y in productBox Q, f y) / volume.real (productBox Q)|) x))

end ReyZygmund
