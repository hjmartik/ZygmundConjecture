import ReyZygmund.MathlibOnly.SquareFunctions

/-!
# Finite projections and cross-coordinate averages

Fix a top rectangle `I` and the smallest side length `2^(-k)`.
`SquareFunctions.lean` defines the coordinate operators and the interior cubes
above this smallest scale. Here we define the finite projection and the
families of cubes used for cross-coordinate averaging.

The sums have real terms and finite index sets under the projection hypotheses;
`∑'` therefore denotes an ordinary finite sum. The projection can take either sign.

For boxes, `P ≤ Q` means containment. `Maximal (· ∈ A) P` means that `P`
is maximal in `A` for this order. `Finset.univ.erase j` selects all coordinates
except `j`.
-/

open BoxIntegral
open scoped BigOperators Classical

namespace ReyZygmund.MathlibOnly

noncomputable section

/-- The finite cube family `D₀`: cubes inside `I` of side at least `2^(-k)`.
The smallest cubes are included. -/
def finiteCubes {d : ℕ} (D : CubeGrid d) (I : Box (Fin d)) (k : ℤ) :
    Set (Box (Fin d)) :=
  {Q | (∃ l : ℤ, -k ≤ l ∧ Q ∈ D.cubes l) ∧ (Q : Set (Fin d → ℝ)) ⊆ I}

/-- The product finite grid, with one cube from `D₀` in each coordinate. -/
def finiteRectangles {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, CubeGrid (d i)) (I : Rectangle d) (k : ℤ) : Set (Rectangle d) :=
  {R | ∀ i, R i ∈ finiteCubes (D i) (I i) k}

/-- Interior rectangles contained in some member of `G`.
The set indexes each rectangle once, even if several members contain it. -/
def removedRectangles {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, CubeGrid (d i)) (I : Rectangle d) (k : ℤ)
    (G : Set (Rectangle d)) : Set (Rectangle d) :=
  {L | (∀ i, L i ∈ interiorCubes (D i) (I i) k) ∧
    ∃ R ∈ G, ∀ i, (L i : Set (Fin (d i) → ℝ)) ⊆ R i}

/-- `F_G = f - ∑_{L ⊆ R ∈ G} Δ_L f`, using the interior finite-grid indices. -/
def projection {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, CubeGrid (d i)) (I : Rectangle d) (k : ℤ)
    (G : Set (Rectangle d)) (f : ProductPoint d → ℝ) (x : ProductPoint d) : ℝ :=
  f x - ∑' L : removedRectangles D I k G, fullDifference L.1 f x

/-- Cubes `R^j` from members of `G` containing `K` in every other coordinate,
together with all bottom cubes of the top factor `I^j`. -/
def crossCandidates {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, CubeGrid (d i)) (I : Rectangle d) (k : ℤ)
    (G : Set (Rectangle d)) (j : Fin m)
    (K : PartialRectangle d (Finset.univ.erase j)) : Set (Box (Fin (d j))) :=
  {P | ∃ R ∈ G, P = R j ∧
    ∀ i : (Finset.univ.erase j : Finset (Fin m)),
      (K i : Set (Fin (d i) → ℝ)) ⊆ R i} ∪ bottomCubes (D j) (I j) k

/-- The maximal candidate cubes. -/
def crossPartition {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, CubeGrid (d i)) (I : Rectangle d) (k : ℤ)
    (G : Set (Rectangle d)) (j : Fin m)
    (K : PartialRectangle d (Finset.univ.erase j)) : Set (Box (Fin (d j))) :=
  {P | Maximal (· ∈ crossCandidates D I k G j K) P}

/-- `X_K g = ∑_{P ∈ P_K} E_P g`, acting only in coordinate `j`.
The partition depends on `G` and the cubes of `K` in the other coordinates. -/
def crossAverage {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, CubeGrid (d i)) (I : Rectangle d) (k : ℤ)
    (G : Set (Rectangle d)) (j : Fin m)
    (K : PartialRectangle d (Finset.univ.erase j))
    (g : ProductPoint d → ℝ) (x : ProductPoint d) : ℝ :=
  ∑' P : crossPartition D I k G j K, coordinateAverage j P.1 g x

/-- The averaging rectangles `B`: members of the finite product grid whose
`j`th factor belongs to the cross partition determined by the other factors,
for at least one coordinate `j`. The other factors may be bottom cubes. -/
def averagingRectangles {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, CubeGrid (d i)) (I : Rectangle d) (k : ℤ)
    (G : Set (Rectangle d)) : Set (Rectangle d) :=
  {R | R ∈ finiteRectangles D I k ∧
    ∃ j, R j ∈ crossPartition D I k G j (fun i => R i)}

end
end ReyZygmund.MathlibOnly
