import ReyZygmund.Geometry.GridFamilies
import ReyZygmund.Geometry.ProductMaps
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

/-! # Full-grid signed averages and differences

These operators range over the whole grid. A full difference expands the product
of child-minus-parent averages into signed rectangle integrals.
`RawDifferenceBridge.lean` identifies it with the coordinate operators;
`GridFiniteExpansion.lean` gives the finite-expansion identities used for the
square theorem.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

open ReyZygmund.MathlibOnly (CubeGrid gridRectangles)

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- The finite rectangles in one term of the full difference expansion:
children in A, and the original cube in the remaining coordinates. -/
noncomputable def differenceRectangles (A : Finset (Fin m))
    (Q : ∀ i, Box (Fin (d i))) : Finset (∀ i, Box (Fin (d i))) :=
  Fintype.piFinset (fun i => if i ∈ A then (Prepartition.splitCenter (Q i)).boxes
    else {Q i})

/-- The full product difference as a finite inclusion–exclusion sum of
supported signed averages. This formula defines the full-grid square function
on arbitrary real-valued inputs. For bounded measurable inputs,
`fullDifference_eq_rawProductDifference` in `RawDifferenceBridge.lean` identifies it
with the composition of coordinate differences in the specification. -/
noncomputable def rawProductDifference (Q : ∀ i, Box (Fin (d i)))
    (g : ProductPoint d → ℝ) (x : ProductPoint d) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset (Fin m)).powerset,
    (-1 : ℝ) ^ (m - A.card) * ∑ R ∈ differenceRectangles A Q,
      (productRectangle R).indicator
        (fun _ => (∫ y in productRectangle R, g y) / volume.real (productRectangle R)) x

/-- The full signed-average maximum. The absolute value is taken after the
signed integral, in contrast with the positive maximal operator. -/
noncomputable def signedGridMaximal (D : ∀ i, CubeGrid (d i))
    (g : ProductPoint d → ℝ) (x : ProductPoint d) : ℝ≥0∞ :=
  ⨆ Q : gridRectangles D, ENNReal.ofReal ((productRectangle Q.val).indicator
    (fun _ => |(∫ y in productRectangle Q.val, g y) / volume.real (productRectangle Q.val)|) x)

/-- The full square function sums over all grid rectangles. Extended
nonnegative summation prevents divergent real sums from defaulting to zero. -/
noncomputable def fullGridSquare (D : ∀ i, CubeGrid (d i))
    (g : ProductPoint d → ℝ) (x : ProductPoint d) : ℝ≥0∞ :=
  (∑' Q : gridRectangles D, (ENNReal.ofReal |rawProductDifference Q.val g x|) ^ 2) ^
    (1 / 2 : ℝ)

end ReyZygmund.Geometry
