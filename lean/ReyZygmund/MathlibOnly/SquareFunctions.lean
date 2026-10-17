import ReyZygmund.MathlibOnly.Definitions
import Mathlib.Analysis.BoxIntegral.Partition.SubboxInduction
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Averages, martingale differences and finite dyadic grids

The operators act in grouped coordinates `x = (x i) : ∏ i, ℝ^(d i)`.
The cube grids and rectangle tuples are those of `Definitions.lean`.

All measures are Lebesgue measure. A box denotes the product of its intervals
`(lower, upper]`, and `volume.real` denotes its volume as a real number.
The signed averages use ordinary real integrals.

Here `∑'` denotes a sum of nonnegative terms, allowing infinity. The full square
function sums over the entire grid; the weighted estimates use finite subgrids.
An index `R : gridRectangles D` is a rectangle together with its membership
in that family; `R.1` denotes the rectangle itself. The expressions `Q.1` and
`K.1` similarly extract a cube or partial rectangle from a restricted index.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.MathlibOnly

noncomputable section

/-- A point of `∏ i, ℝ^(d i)`, with its coordinates grouped into cube factors. -/
abbrev ProductPoint {m : ℕ} (d : Fin m → ℕ) := ∀ i, Fin (d i) → ℝ

/-- The product of the box factors, in grouped coordinates. -/
def productRectangle {m : ℕ} {d : Fin m → ℕ} (R : Rectangle d) :
    Set (ProductPoint d) :=
  {x | ∀ i, x i ∈ (R i : Set (Fin (d i) → ℝ))}

/-- The signed average `⟨u⟩_Q = |Q|⁻¹ ∫_Q u`. -/
def cubeMean {d : ℕ} (Q : Box (Fin d)) (u : (Fin d → ℝ) → ℝ) : ℝ :=
  (∫ x in (Q : Set (Fin d → ℝ)), u x ∂volume) /
    volume.real (Q : Set (Fin d → ℝ))

/-- The averaging operator `E_Q u = 1_Q ⟨u⟩_Q`. -/
def cubeAverage {d : ℕ} (Q : Box (Fin d)) (u : (Fin d → ℝ) → ℝ) :
    (Fin d → ℝ) → ℝ :=
  (Q : Set (Fin d → ℝ)).indicator (fun _ => cubeMean Q u)

/-- `Δ_Q u = ∑_{J ∈ ch(Q)} E_J u - E_Q u`.
`splitCenter Q` cuts each side at its midpoint, giving the `2^d` children. -/
def cubeDifference {d : ℕ} (Q : Box (Fin d)) (u : (Fin d → ℝ) → ℝ) :
    (Fin d → ℝ) → ℝ :=
  (∑ J ∈ (Prepartition.splitCenter Q).boxes, cubeAverage J u) - cubeAverage Q u

/-- `E_Q` acting in coordinate `i`. `Function.update x i y` replaces the
`i`th coordinate block of `x` by `y` and leaves the other blocks unchanged. -/
def coordinateAverage {m : ℕ} {d : Fin m → ℕ} (i : Fin m)
    (Q : Box (Fin (d i))) (f : ProductPoint d → ℝ) (x : ProductPoint d) : ℝ :=
  cubeAverage Q (fun y => f (Function.update x i y)) (x i)

/-- `Δ_Q` acting in coordinate `i`, with the other blocks held fixed. -/
def coordinateDifference {m : ℕ} {d : Fin m → ℕ} (i : Fin m)
    (Q : Box (Fin (d i))) (f : ProductPoint d → ℝ) (x : ProductPoint d) : ℝ :=
  cubeDifference Q (fun y => f (Function.update x i y)) (x i)

/-- A tuple `K^A = (K^i)_{i ∈ A}` of box factors in the selected coordinates.
An index `i : A` consists of a coordinate index and the assertion that it lies in `A`. -/
abbrev PartialRectangle {m : ℕ} (d : Fin m → ℕ) (A : Finset (Fin m)) :=
  ∀ i : A, Box (Fin (d i))

/-- `E_{K^A} = ∏_{i ∈ A} E_{K^i}`. The sorted list and `foldr` express
composition in increasing coordinate order: `E_{i₁}(E_{i₂}(… f))`.
For an empty coordinate set this is the identity. -/
def partialAverage {m : ℕ} {d : Fin m → ℕ} (A : Finset (Fin m))
    (K : PartialRectangle d A) (f : ProductPoint d → ℝ) : ProductPoint d → ℝ :=
  ((Finset.univ : Finset A).sort (· ≤ ·)).foldr
    (fun i g => coordinateAverage i.1 (K i) g) f

/-- The full averaging operator `E_R = ∏_i E_{R^i}`. -/
def fullAverage {m : ℕ} {d : Fin m → ℕ} (R : Rectangle d)
    (f : ProductPoint d → ℝ) : ProductPoint d → ℝ :=
  partialAverage Finset.univ (fun i => R i) f

/-- `Δ_{K^A} = ∏_{i ∈ A} Δ_{K^i}`, composed in the same coordinate order.
Coordinates outside `A` are left unchanged. -/
def partialDifference {m : ℕ} {d : Fin m → ℕ} (A : Finset (Fin m))
    (K : PartialRectangle d A) (f : ProductPoint d → ℝ) : ProductPoint d → ℝ :=
  ((Finset.univ : Finset A).sort (· ≤ ·)).foldr
    (fun i g => coordinateDifference i.1 (K i) g) f

/-- The full product martingale difference `Δ_R = ∏_i Δ_{R^i}`. -/
def fullDifference {m : ℕ} {d : Fin m → ℕ} (R : Rectangle d)
    (f : ProductPoint d → ℝ) : ProductPoint d → ℝ :=
  partialDifference Finset.univ (fun i => R i) f

/-- `M_G f(x) = sup_{R ∈ G, x ∈ R} |R|⁻¹ ∫_R |f|`, in grouped coordinates,
with values in `[0, ∞]`. -/
def productMaximal {m : ℕ} {d : Fin m → ℕ} (G : Set (Rectangle d))
    (f : ProductPoint d → ℝ) (x : ProductPoint d) : ℝ≥0∞ :=
  ⨆ R ∈ G, ⨆ (_ : x ∈ productRectangle R),
    (∫⁻ y in productRectangle R, ENNReal.ofReal |f y| ∂volume) /
      volume (productRectangle R)

/-- The signed dyadic maximal function `sup_{R ∋ x} |⟨g⟩_R|`, with values
in `[0, ∞]`. The absolute value is taken after the integral. -/
def signedMaximal {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, CubeGrid (d i))
    (g : ProductPoint d → ℝ) (x : ProductPoint d) : ℝ≥0∞ :=
  ⨆ R ∈ gridRectangles D, ⨆ (_ : x ∈ productRectangle R),
    ENNReal.ofReal |(∫ y in productRectangle R, g y ∂volume) /
      volume.real (productRectangle R)|

/-- `S_D g = (∑_{R ∈ D} |Δ_R g|²)^(1/2)`, with values in `[0, ∞]`. -/
def squareFunction {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, CubeGrid (d i))
    (g : ProductPoint d → ℝ) (x : ProductPoint d) : ℝ≥0∞ :=
  (∑' R : gridRectangles D, ENNReal.ofReal |fullDifference R.1 g x| ^ 2) ^ (1 / 2 : ℝ)

/-- The smallest cubes in `I`: cubes of the grid at side length `2^(-k)`. -/
def bottomCubes {d : ℕ} (D : CubeGrid d) (I : Box (Fin d)) (k : ℤ) :
    Set (Box (Fin d)) :=
  {Q | Q ∈ D.cubes (-k) ∧ (Q : Set (Fin d → ℝ)) ⊆ I}

/-- The cubes strictly above the smallest scale, contained in `I`.
These are the difference indices `(D₀)°`; the bottom cubes are excluded.
Here “interior” refers to the scale range, not the geometric interior of `I`. -/
def interiorCubes {d : ℕ} (D : CubeGrid d) (I : Box (Fin d)) (k : ℤ) :
    Set (Box (Fin d)) :=
  {Q | (∃ l : ℤ, -k < l ∧ Q ∈ D.cubes l) ∧ (Q : Set (Fin d → ℝ)) ⊆ I}

/-- Constancy on each smallest cube in `I`; the values on distinct cubes may differ. -/
def ConstantOnBottomCubes {d : ℕ} (D : CubeGrid d) (I : Box (Fin d))
    (k : ℤ) (u : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ Q ∈ bottomCubes D I k, ∀ x ∈ Q, ∀ y ∈ Q, u x = u y

/-- Constancy on every product of smallest cubes in the top rectangle.
The same side-length cutoff `2^(-k)` is used in every coordinate. -/
def ConstantOnBottomRectangles {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, CubeGrid (d i)) (I : Rectangle d) (k : ℤ)
    (f : ProductPoint d → ℝ) : Prop :=
  ∀ J : Rectangle d, (∀ i, J i ∈ bottomCubes (D i) (I i) k) →
    ∀ x ∈ productRectangle J, ∀ y ∈ productRectangle J, f x = f y

/-- The partial rectangle indices `(D₀^A)°`, with one interior cube for each `i ∈ A`. -/
def partialInterior {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, CubeGrid (d i)) (I : Rectangle d) (k : ℤ) (A : Finset (Fin m)) :
    Set (PartialRectangle d A) :=
  {K | ∀ i : A, K i ∈ interiorCubes (D i) (I i) k}

/-- `S_A g = (∑_{K^A ∈ (D₀^A)°} |Δ_{K^A} g|²)^(1/2)`.
Only the selected coordinates are differenced, and the smallest scale is
excluded. The sum is finite under the hypotheses on the top rectangle and cutoff. -/
def partialSquareFunction {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, CubeGrid (d i)) (I : Rectangle d) (k : ℤ) (A : Finset (Fin m))
    (g : ProductPoint d → ℝ) (x : ProductPoint d) : ℝ≥0∞ :=
  (∑' K : partialInterior D I k A,
    ENNReal.ofReal |partialDifference A K.1 g x| ^ 2) ^ (1 / 2 : ℝ)

/-- `W g = (∑_j (S_{A_j} g)²)^(1/2)`, where `A_j` omits coordinate `j`.
Each summand is a square function in the other `m - 1` coordinates. -/
def combinedSquareFunction {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, CubeGrid (d i)) (I : Rectangle d) (k : ℤ)
    (g : ProductPoint d → ℝ) (x : ProductPoint d) : ℝ≥0∞ :=
  (∑ j : Fin m, partialSquareFunction D I k (Finset.univ.erase j) g x ^ 2) ^
    (1 / 2 : ℝ)

/-- The integration region `K^A × I^(Aᶜ)`: selected factors come from `K`,
and the other factors remain those of the top rectangle `I`. -/
def partialRectangleRegion {m : ℕ} {d : Fin m → ℕ} (I : Rectangle d)
    (A : Finset (Fin m)) (K : PartialRectangle d A) : Set (ProductPoint d) :=
  {x | ∀ i, if hi : i ∈ A then x i ∈ (K ⟨i, hi⟩ : Set (Fin (d i) → ℝ))
    else x i ∈ (I i : Set (Fin (d i) → ℝ))}

end
end ReyZygmund.MathlibOnly
