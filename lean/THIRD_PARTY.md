# Third-party sources and acknowledgments

## Mathlib: dependency and adapted helpers

This formalization uses Lean and Mathlib. Ordinary imports of their declarations
are distinct from the source adaptation below. Preserve the upstream licenses
and notices when redistributing dependency sources.

The private partial-integral helpers in
[Geometry/ProductMean.lean](ReyZygmund/Geometry/ProductMean.lean) adapt the
finite-product decomposition in Mathlib's
[MeasureTheory/Integral/Marginal.lean](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/MeasureTheory/Integral/Marginal.lean),
especially `lmarginal_singleton`, `lmarginal_union` and `lmarginal_insert`.

Original notice for the adapted portions:

> Copyright (c) 2023 Floris van Doorn. All rights reserved.
> Released under Apache 2.0 license as described in the file LICENSE.
> Authors: Floris van Doorn, Heather Macbeth

The adaptation specializes to restricted Lebesgue measures on boxes, replaces
nonnegative integrals by signed Bochner integrals, and proves the required
integrability from a bound on the input. The source header retains this notice,
the exact upstream revision and the modification summary. A verbatim copy of
Mathlib's license is included in [LICENSES/Apache-2.0.txt](LICENSES/Apache-2.0.txt).

## Carleson: proof-pattern acknowledgment

The finite maximal-cube selection argument in
[Geometry/FinitePartition.lean](ReyZygmund/Geometry/FinitePartition.lean) was
informed by `Grid.maxCubes`, `exists_maximal_supercube` and
`maxCubes_pairwiseDisjoint` in the Carleson project's
[GridStructure.lean](https://github.com/fpvandoorn/carleson/blob/affd6dda5d4b97ef2ca68148a5bd5c906d828a6c/Carleson/GridStructure.lean).
Our implementation works with concrete boxes and invokes Mathlib's
`Finset.exists_le_maximal`; it does not import Carleson or copy those proof
bodies verbatim. We acknowledge this idea and proof-pattern reference.

Project-authored code and accompanying documentation are also released under
[Apache-2.0](../LICENSE). This does not replace the retained notices above or
change the licenses of separately obtained dependencies.
