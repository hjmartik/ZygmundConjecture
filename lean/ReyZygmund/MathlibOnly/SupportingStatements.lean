import ReyZygmund.MathlibOnly.Projections
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Finset.Powerset

/-!
# Supporting and additional results

`Definitions.lean` supplies the geometry, families, maximal and overlap
functions. `SquareFunctions.lean` supplies averages, differences and finite
grids; `Projections.lean` supplies the projection and cross-coordinate averages.

The [definition guide](DEFINITIONS.md#maximal-and-overlap-functions) explains
the norm and integral notation. Function equalities are pointwise.
`totalDim` is the sum of the block dimensions.

In the slicing, endpoint, overlap and sharpness statements, `n = m - 1`:
there are `n` initial cube factors and one last factor. The square-function,
projection and selection statements use `m` for the total number of cube factors.
`Fin m` indexes these factors from `0` to `m - 1`.
-/

open BoxIntegral MeasureTheory Filter
open scoped BigOperators ENNReal Classical Topology

namespace ReyZygmund.MathlibOnly

noncomputable section

/-! ## Square-function estimates -/

/-- The maximal function formed from signed averages is bounded in `L^p`
by the product square function for `1 ≤ p ≤ 3/2`.
The input has a finite martingale expansion; both operators use the whole grid. -/
def MaximalSquareFunctionEstimate : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (d : Fin m → ℕ), (∀ i, 0 < d i) →
    ∀ (D : ∀ i, CubeGrid (d i)) (H : Finset (Rectangle d)),
      (H : Set (Rectangle d)) ⊆ gridRectangles D →
      ∀ (g : ProductPoint d → ℝ),
        g = (fun x => ∑ R ∈ H, fullDifference R g x) →
        ∀ (p : ℝ), 1 ≤ p → p ≤ 3 / 2 →
          eLpNorm (signedMaximal D g) (ENNReal.ofReal p) volume ≤
            ENNReal.ofReal ((2 : ℝ) ^ (6 * (∑ i, d i) + 10)) *
              eLpNorm (squareFunction D g) (ENNReal.ofReal p) volume

/-- The scalar remainder estimate for `Ψₚ(a,b) = a² / b^(2-p)`.
Real exponents use the ordinary real power on positive bases. -/
def ScalarEstimate : Prop :=
  ∀ (p a h b eta : ℝ), 1 < p → p ≤ 2 → 0 < b → 0 < b + eta →
    (p - 1) / (3 - p) * (h ^ 2 / (max b (b + eta)) ^ (2 - p)) ≤
      (a + h) ^ 2 / (b + eta) ^ (2 - p) - a ^ 2 / b ^ (2 - p) -
        2 * a * h / b ^ (2 - p) + (2 - p) * a ^ 2 * eta / b ^ (3 - p)

/-- The weighted square-function estimate for `1 < p ≤ 2` on a finite
dyadic grid in `ℝ^d`, with inputs constant on bottom cubes and a positive weight. -/
def WeightedSquareFunctionEstimate : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (D : CubeGrid d) (I : Box (Fin d)) (k : ℤ),
    (∃ l : ℤ, I ∈ D.cubes l ∧ -k ≤ l) →
    ∀ (u v : (Fin d → ℝ) → ℝ),
      ConstantOnBottomCubes D I k u → ConstantOnBottomCubes D I k v →
      (∀ x ∈ I, 0 < v x) →
      ∀ (p : ℝ), 1 < p → p ≤ 2 →
        (∑' Q : interiorCubes D I k,
          ∫⁻ x in (Q.1 : Set (Fin d → ℝ)),
            ENNReal.ofReal ((cubeDifference Q.1 u x) ^ 2 /
              (cubeMean Q.1 v) ^ (2 - p)) ∂volume) ≤
          ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) * (2 - p)) * ((3 - p) / (p - 1))) *
            ∫⁻ x in (I : Set (Fin d → ℝ)),
              ENNReal.ofReal ((u x) ^ 2 / (v x) ^ (2 - p)) ∂volume

/-- The product weighted square-function estimate for a nonempty coordinate
set `A` and `1 < p ≤ 2`, on finite grids with a common smallest scale. -/
def ProductWeightedSquareFunctionEstimate : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (d : Fin m → ℕ), (∀ i, 0 < d i) →
    ∀ (D : ∀ i, CubeGrid (d i)) (I : Rectangle d) (k : ℤ),
      (∀ i, ∃ l : ℤ, I i ∈ (D i).cubes l ∧ -k ≤ l) →
      ∀ (f : ProductPoint d → ℝ),
        (∀ x ∉ productRectangle I, f x = 0) →
        (∀ x ∈ productRectangle I, 0 < f x) →
        ConstantOnBottomRectangles D I k f →
        ∀ (A : Finset (Fin m)), A.Nonempty →
          ∀ (p : ℝ), 1 < p → p ≤ 2 →
            (∑' K : partialInterior D I k A,
              ∫⁻ x in partialRectangleRegion I A K.1,
                ENNReal.ofReal ((partialDifference A K.1 f x) ^ 2 /
                  (partialAverage A K.1 f x) ^ (2 - p)) ∂volume) ≤
              ENNReal.ofReal ((2 : ℝ) ^ ((2 - p) * ∑ i ∈ A, (d i : ℝ)) *
                ((3 - p) / (p - 1)) ^ A.card) *
                  eLpNorm f (ENNReal.ofReal p) volume ^ p

/-! ## Projection identities and estimates -/

/-- The projection preserves the averages on a weakly incomparable family.
The equality of the averaging operators is pointwise. -/
def ProjectionPreservesAverages : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (d : Fin m → ℕ), (∀ i, 0 < d i) →
    ∀ (D : ∀ i, CubeGrid (d i)) (I : Rectangle d) (k : ℤ),
      (∀ i, ∃ l : ℤ, I i ∈ (D i).cubes l ∧ -k ≤ l) →
      ∀ (f : ProductPoint d → ℝ),
        (∀ x ∉ productRectangle I, f x = 0) →
        (∀ x ∈ productRectangle I, 0 < f x) →
        ConstantOnBottomRectangles D I k f →
        ∀ (G : Set (Rectangle d)), G ⊆ finiteRectangles D I k →
          WeaklyIncomparable G → ∀ R ∈ G,
            fullAverage R f = fullAverage R (projection D I k G f)

/-- On each rectangle of the family, the average of the projection is a signed
sum of its averages over proper coordinate subsets. The empty subset gives
the identity operator. -/
def ProjectionPartialAverages : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (d : Fin m → ℕ), (∀ i, 0 < d i) →
    ∀ (D : ∀ i, CubeGrid (d i)) (I : Rectangle d) (k : ℤ),
      (∀ i, ∃ l : ℤ, I i ∈ (D i).cubes l ∧ -k ≤ l) →
      ∀ (f : ProductPoint d → ℝ),
        (∀ x ∉ productRectangle I, f x = 0) →
        (∀ x ∈ productRectangle I, 0 < f x) →
        ConstantOnBottomRectangles D I k f →
        ∀ (G : Set (Rectangle d)), G ⊆ finiteRectangles D I k →
          let F := projection D I k G f
          ∀ R ∈ G, ∀ x ∈ productRectangle R,
            fullAverage R F x =
              ∑ B ∈ (Finset.univ : Finset (Fin m)).ssubsets,
                (-1 : ℝ) ^ (m + 1 + B.card) * partialAverage B (fun i => R i) F x

/-- Partial differences of the projection are cross averages of those of `f`.
The partial rectangle omits coordinate `j`; the identity holds pointwise. -/
def ProjectionDifferences : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (d : Fin m → ℕ), (∀ i, 0 < d i) →
    ∀ (D : ∀ i, CubeGrid (d i)) (I : Rectangle d) (k : ℤ),
      (∀ i, ∃ l : ℤ, I i ∈ (D i).cubes l ∧ -k ≤ l) →
      ∀ (f : ProductPoint d → ℝ),
        (∀ x ∉ productRectangle I, f x = 0) →
        (∀ x ∈ productRectangle I, 0 < f x) →
        ConstantOnBottomRectangles D I k f →
        ∀ (G : Set (Rectangle d)), G ⊆ finiteRectangles D I k →
          ∀ (j : Fin m) (K : PartialRectangle d (Finset.univ.erase j)),
            (∀ i : (Finset.univ.erase j : Finset (Fin m)),
              K i ∈ finiteCubes (D i) (I i) k) →
            partialDifference (Finset.univ.erase j) K (projection D I k G f) =
              crossAverage D I k G j K (partialDifference (Finset.univ.erase j) K f)

/-- Adding the averaging rectangles leaves the projection unchanged.
If the original family is weakly incomparable, so is the enlarged family. -/
def AveragingFamilyGeometry : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (d : Fin m → ℕ), (∀ i, 0 < d i) →
    ∀ (D : ∀ i, CubeGrid (d i)) (I : Rectangle d) (k : ℤ),
      (∀ i, ∃ l : ℤ, I i ∈ (D i).cubes l ∧ -k ≤ l) →
      ∀ (f : ProductPoint d → ℝ),
        (∀ x ∉ productRectangle I, f x = 0) →
        (∀ x ∈ productRectangle I, 0 < f x) →
        ConstantOnBottomRectangles D I k f →
        ∀ (G : Set (Rectangle d)), G ⊆ finiteRectangles D I k →
          let Ghat := G ∪ averagingRectangles D I k G
          projection D I k Ghat f = projection D I k G f ∧
            (WeaklyIncomparable G → WeaklyIncomparable Ghat)

/-- Averages of `f` on the enlarged family are signed sums of partial averages
of its projection.
The sum includes every proper coordinate subset, including the empty set.
The equality holds on each rectangle of the enlarged family. -/
def RepresentationOfAverages : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (d : Fin m → ℕ), (∀ i, 0 < d i) →
    ∀ (D : ∀ i, CubeGrid (d i)) (I : Rectangle d) (k : ℤ),
      (∀ i, ∃ l : ℤ, I i ∈ (D i).cubes l ∧ -k ≤ l) →
      ∀ (f : ProductPoint d → ℝ),
        (∀ x ∉ productRectangle I, f x = 0) →
        (∀ x ∈ productRectangle I, 0 < f x) →
        ConstantOnBottomRectangles D I k f →
        ∀ (G : Set (Rectangle d)), G ⊆ finiteRectangles D I k →
          WeaklyIncomparable G →
          let F := projection D I k G f
          ∀ R ∈ G ∪ averagingRectangles D I k G, ∀ x ∈ productRectangle R,
            fullAverage R f x =
              ∑ B ∈ (Finset.univ : Finset (Fin m)).ssubsets,
                (-1 : ℝ) ^ (m + 1 + B.card) * partialAverage B (fun i => R i) F x

/-- The maximal function of the enlarged family is bounded in `L^p` by the
norms of `f` and `W F` for `1 < p ≤ 3/2`, where `F` is the projection.
Here `p / (p - 1)` is the conjugate exponent `p'`. -/
def MaximalSquareFunctionReduction : Prop :=
  ∀ (m totalDim : ℕ), 2 ≤ m → ∃ C : ℝ, 0 < C ∧
    ∀ (d : Fin m → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
      ∀ (D : ∀ i, CubeGrid (d i)) (I : Rectangle d) (k : ℤ),
        (∀ i, ∃ l : ℤ, I i ∈ (D i).cubes l ∧ -k ≤ l) →
        ∀ (f : ProductPoint d → ℝ),
          (∀ x ∉ productRectangle I, f x = 0) →
          (∀ x ∈ productRectangle I, 0 < f x) →
          ConstantOnBottomRectangles D I k f →
          ∀ (G : Set (Rectangle d)), G ⊆ finiteRectangles D I k →
            WeaklyIncomparable G → ∀ (p : ℝ), 1 < p → p ≤ 3 / 2 →
              let F := projection D I k G f
              let Ghat := G ∪ averagingRectangles D I k G
              eLpNorm (productMaximal Ghat f) (ENNReal.ofReal p) volume ≤
                ENNReal.ofReal (C * (p / (p - 1)) ^ (m - 2)) *
                    eLpNorm f (ENNReal.ofReal p) volume +
                  ENNReal.ofReal C *
                    eLpNorm (combinedSquareFunction D I k F) (ENNReal.ofReal p) volume

/-- The weighted square-function estimate for the projected function, `1 < p ≤ 2`.
The denominator is the maximal function over the averaging rectangles `B`. -/
def ProjectedSquareFunctionEstimate : Prop :=
  ∀ (m totalDim : ℕ), 2 ≤ m → ∃ C : ℝ, 0 < C ∧
    ∀ (d : Fin m → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
      ∀ (D : ∀ i, CubeGrid (d i)) (I : Rectangle d) (k : ℤ),
        (∀ i, ∃ l : ℤ, I i ∈ (D i).cubes l ∧ -k ≤ l) →
        ∀ (f : ProductPoint d → ℝ),
          (∀ x ∉ productRectangle I, f x = 0) →
          (∀ x ∈ productRectangle I, 0 < f x) →
          ConstantOnBottomRectangles D I k f →
          ∀ (G : Set (Rectangle d)), G ⊆ finiteRectangles D I k →
            ∀ (p : ℝ), 1 < p → p ≤ 2 →
              let F := projection D I k G f
              let B := averagingRectangles D I k G
              (∫⁻ x in productRectangle I,
                combinedSquareFunction D I k F x ^ 2 /
                  productMaximal B f x ^ (2 - p) ∂volume) ≤
                ENNReal.ofReal (C * (p / (p - 1)) ^ (m - 1)) *
                  eLpNorm f (ENNReal.ofReal p) volume ^ p

/-! ## Covering, selection and slicing -/

/-- Every closed cube of side `s` lies in a cube of side `2 ^ rounding s`
from one of the `3^d` alternating shifted grids.
`Set.Icc Q.lower Q.upper` is the closed cube with the corners of `Q`. -/
def PrescribedScaleCovering : Prop :=
  ∀ (d : ℕ), 0 < d →
    ∃ D : (Fin d → Fin 3) → CubeGrid d,
      (∀ tau k, (D tau).cubes k = shiftedCubes tau k) ∧
      (∀ tau, IcoGrid (D tau)) ∧
      ∀ (s : ℝ), 0 < s → ∀ (Q : Box (Fin d)),
        (∀ j, Q.upper j - Q.lower j = s) →
        ∃ (tau : Fin d → Fin 3) (P : Box (Fin d)),
          P ∈ (D tau).cubes (rounding s) ∧
            Set.Icc Q.lower Q.upper ⊆ cubeIco P

/-- Córdoba–Fefferman selection with comparable shadow and a constant depending
only on the number of factors. Each selected rectangle meets the union of
the other selected rectangles in at most half its measure. -/
def CordobaFeffermanSelection : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∃ C : ℝ, 0 < C ∧
    ∀ (d : Fin m → ℕ), (∀ i, 0 < d i) →
      ∀ (D : ∀ i, CubeGrid (d i)) (F : Set (Rectangle d)),
        F.Finite → F ⊆ gridRectangles D →
        ∃ G ⊆ F, volume (shadow F) ≤ ENNReal.ofReal C * volume (shadow G) ∧
          ∀ R ∈ G,
            volume (rectangle R ∩ shadow (G \ {R})) ≤
              (1 / 2 : ℝ≥0∞) * volume (rectangle R)

/-- Slices of an incomparable rounded family are weakly incomparable.
Each projected rectangle has a unique original rectangle through `t`, and
the slice overlap equals the original overlap pointwise, using `[lower, upper)` boundaries. -/
def WeaklyIncomparableSlices : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) →
    ∀ (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)), Monotone phi →
      ∀ (tau : ∀ i, Fin (d i) → Fin 3) (G : Set (Rectangle d)),
        G ⊆ roundedRectangles tau phi →
        (∀ R ∈ G, ∀ S ∈ G, rectangleIco R ⊆ rectangleIco S → R = S) →
        ∀ (t : Fin (d (Fin.last n)) → ℝ),
          let Gt := sliceFamilyIco G t
          (∀ P ∈ Gt, ∀ Q ∈ Gt, ¬ ∀ i, cubeIco (P i) ⊂ cubeIco (Q i)) ∧
          (∀ P ∈ Gt,
            ∃! R, R ∈ G ∧ t ∈ cubeIco (R (Fin.last n)) ∧ initialProjection R = P) ∧
          ∀ x : Point (fun i : Fin n => d i.castSucc),
            overlapIco G (appendLastPoint x t) = overlapIco Gt x

/-- Slices of a finite product-grid family satisfying the half-overlap condition
are `1/2`-sparse. -/
def HalfSparseSlices : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) →
    ∀ (D : ∀ i, CubeGrid (d i)) (G : Set (Rectangle d)),
      G.Finite → G ⊆ gridRectangles D →
      (∀ R ∈ G,
        volume (rectangle R ∩ shadow (G \ {R})) ≤
          (1 / 2 : ℝ≥0∞) * volume (rectangle R)) →
      ∀ (t : Fin (d (Fin.last n)) → ℝ), Sparse (1 / 2) (sliceFamily G t)

/-! ## Endpoint, overlap and sharpness results -/

/-- The rounded dyadic endpoint estimate in each prescribed shifted grid.
The constant depends only on the number of factors and total dimension,
uniformly in `phi` and `tau`. -/
def RoundedDyadicEndpointEstimate : Prop :=
  ∀ (n totalDim : ℕ), 2 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
      ∀ (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)), Monotone phi →
        ∀ (tau : ∀ i, Fin (d i) → Fin 3),
          ∀ (f : Point d → ℝ), LocallyIntegrable f volume →
            ∀ (lam : ℝ), 0 < lam →
              volume {x | ENNReal.ofReal lam < maximalIco (roundedRectangles tau phi) f x} ≤
                ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
                  (|f x| / lam * (Real.log (Real.exp 1 + |f x| / lam)) ^ (n - 1))
                    ∂volume

/-- The dyadic Zygmund endpoint estimate for every product of dyadic cube grids
and every coordinatewise nondecreasing integer scale relation `Phi`.
The constant depends only on the number of factors and total dimension. -/
def DyadicZygmundConjecture : Prop :=
  ∀ (n totalDim : ℕ), 2 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
      ∀ (D : ∀ i, CubeGrid (d i)) (Phi : (Fin n → ℤ) → ℤ), Monotone Phi →
        ∀ (f : Point d → ℝ), LocallyIntegrable f volume →
          ∀ (lam : ℝ), 0 < lam →
            volume {x | ENNReal.ofReal lam < maximal (dyadicZygmundRectangles D Phi) f x} ≤
              ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
                (|f x| / lam * (Real.log (Real.exp 1 + |f x| / lam)) ^ (n - 1)) ∂volume

/-- Sparse Φ-Zygmund exponential overlap.
The constants depend only on the number of factors, total dimension and `eta`. -/
def SparsePhiZygmundOverlapEstimate : Prop :=
  ∀ (n totalDim : ℕ), 2 ≤ n → ∀ (eta : ℝ), 0 < eta → eta ≤ 1 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
        ∀ (grids : ∀ i, CubeGrid (d i)) (Phi : (Fin n → ℤ) → ℤ), Monotone Phi →
          ∀ (G : Set (Rectangle d)),
            G ⊆ dyadicZygmundRectangles grids Phi → Sparse eta G → volume (shadow G) < ∞ →
              (∫⁻ x in shadow G,
                exp (ENNReal.ofReal c * overlap G x ^ (1 / (n : ℝ))) ∂volume) ≤
                  ENNReal.ofReal C * volume (shadow G)

/-- Sharpness for the classical dyadic Zygmund family, with `Phi k = ∑ i, k i`.
For every choice of grids and `0 < eta < 1`, one sequence of finite incomparable
sparse families has shadows of measure one and divergent exponential integrals
for every positive coefficient and every power above `1 / n`.
The real indicator sum is the overlap of the finite family. -/
def ClassicalDyadicZygmundSharpness : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) →
    ∀ (grids : ∀ i, CubeGrid (d i)) (eta : ℝ), 0 < eta → eta < 1 →
      ∃ G : ℕ → Finset (Rectangle d),
        (∀ N : ℕ, 2 ≤ N →
          (G N : Set (Rectangle d)) ⊆
              dyadicZygmundRectangles grids (fun k : Fin n → ℤ => ∑ i, k i) ∧
            Incomparable (G N : Set (Rectangle d)) ∧
            Sparse eta (G N : Set (Rectangle d)) ∧
            volume (shadow (G N : Set (Rectangle d))) = 1) ∧
        ∀ (c beta : ℝ), 0 < c → 1 / (n : ℝ) < beta →
          Tendsto (fun N : ℕ =>
            ∫ x in shadow (G N : Set (Rectangle d)),
              Real.exp (c * Real.rpow
                (∑ R ∈ G N, (rectangle R).indicator (fun _ => (1 : ℝ)) x) beta)
                  ∂volume) atTop atTop

end
end ReyZygmund.MathlibOnly
