import ReyZygmund.Geometry.FiniteAverages
import Mathlib.Topology.Bases

/-! # Dyadic grids of half-open Euclidean cubes

Generation `n` partitions the space into cubes of side `2 ^ (-n)`. Bisecting each
side gives the dyadic children at generation `n + 1`. These properties define a
grid. Countability and finite localization are proved later; a common ancestor is
not assumed. The boxes use `(lower, upper]`; `Continuous/HalfOpenBoundary.lean`
and `Continuous/Convention.lean` treat the alternative convention.


-/

open BoxIntegral
open scoped Classical

namespace ReyZygmund.Geometry

/-- A dyadic grid of Euclidean cubes. `StandardGrid.lean` and `ShiftedGrid.lean`
construct examples; `GridDescendants.lean` identifies their finite descendants.
-/
structure DyadicGrid (d : ℕ) where
  cubes : ℤ → Set (Box (Fin d))
  width : ∀ (n : ℤ) (Q : Box (Fin d)), Q ∈ cubes n →
    ∀ i, Q.upper i - Q.lower i = (2 : ℝ) ^ (-n)
  disjoint : ∀ n, (cubes n).Pairwise
    (fun Q R => Disjoint (Q : Set (Fin d → ℝ)) (R : Set (Fin d → ℝ)))
  cover : ∀ (n : ℤ) (x : Fin d → ℝ), ∃ Q ∈ cubes n, x ∈ Q
  children : ∀ (n : ℤ) (Q : Box (Fin d)), Q ∈ cubes n →
    ∀ R ∈ Prepartition.splitCenter Q, R ∈ cubes (n + 1)

end ReyZygmund.Geometry
