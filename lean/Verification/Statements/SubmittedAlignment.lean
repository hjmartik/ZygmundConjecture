import ReyZygmund.MathlibOnly.SubmittedDefinitions
import ReyZygmund.Maximal.Represented
import ReyZygmund.Geometry.SourceCutoff
import ReyZygmund.Geometry.LastCoordinate
import ReyZygmund.Geometry.RawDifferenceBridge
import ReyZygmund.Overlap.Countable

/-!
# Explicit type contracts for the supporting lemmas

These are separately written statements of the reviewed helper theorems.
They protect argument, quantifier and conclusion correspondence during checking.
They reference implementation definitions and are distinct from the six
independent Mathlib-only specifications. No contract is inferred from a theorem
constant or defined by selecting a proof's result type.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical
open ReyZygmund ReyZygmund.Geometry ReyZygmund.Projection
open ReyZygmund.MathlibOnly
open ReyZygmund.MathlibOnly.Submitted

namespace ReyZygmundVerification.SubmittedAlignment

/-- Explicit type for `ReyZygmund.MathlibOnly.Submitted.rectangle_subset_iff`. -/
def MathlibOnly_Submitted_rectangle_subset_iffContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (R S : ∀ i, Box (Fin (d i))),
    rectangle R ⊆ rectangle S ↔ ∀ i, R i ≤ S i

/-- Explicit type for `ReyZygmund.MathlibOnly.Submitted.weaklyIncomparable_iff_equalFactor`. -/
def MathlibOnly_Submitted_weaklyIncomparable_iff_equalFactorContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i)))),
    WeaklyIncomparable G ↔ HasEqualFactorOnContainment G

/-- Explicit type for `ReyZygmund.Projection.weaklyIncomparable_preserves_averages`. -/
def Projection_weaklyIncomparable_preserves_averagesContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (_hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (_hG : G ⊆ productDescendants I N)
    (_hweak : WeaklyIncomparable (G : Set (∀ i, Box (Fin (d i)))))
    (R : ∀ i, Box (Fin (d i))) (_hR : R ∈ G),
    productAverageMap Finset.univ R * finiteProjectionMap I N G =
      productAverageMap Finset.univ R

/-- Explicit type for `ReyZygmund.Projection.finite_lower_coordinate_averages`. -/
def Projection_finite_lower_coordinate_averagesContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (_hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (_hG : G ⊆ productDescendants I N)
    (R : ∀ i, Box (Fin (d i))) (_hR : R ∈ G)
    (F : boundedMeasurableFunctions d) (_hf : ProductLeafConstant I N F.1)
    (_hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (x : ProductPoint d) (_hx : x ∈ productBox R),
    (productAverageMap Finset.univ R (finiteProjectionMap I N G F)).1 x =
      ∑ A ∈ ((Finset.univ : Finset (Fin m)).powerset.erase Finset.univ),
        (-1 : ℝ) ^ (m + 1 + A.card) *
          (productAverageMap A R (finiteProjectionMap I N G F)).1 x

/-- Explicit type for `ReyZygmund.Projection.removedIndices_union_averagingRectangles`. -/
def Projection_removedIndices_union_averagingRectanglesContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (_hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))),
    removedIndices I N (G ∪ averagingRectangles I N G) = removedIndices I N G

/-- Explicit type for `ReyZygmund.Projection.finiteProjectionMap_union_averagingRectangles`. -/
def Projection_finiteProjectionMap_union_averagingRectanglesContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (_hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))),
    finiteProjectionMap I N (G ∪ averagingRectangles I N G) =
      finiteProjectionMap I N G

/-- Explicit type for `ReyZygmund.Projection.averagingRectangle_interior_below_original`. -/
def Projection_averagingRectangle_interior_below_originalContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (_hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (R : ∀ i, Box (Fin (d i)))
    (_hR : R ∈ averagingRectangles I N G) (_hRi : R ∈ productInterior I N),
    ∃ J ∈ G, ∀ i, R i ≤ J i

/-- Explicit type for `ReyZygmund.Projection.averagingRectangle_equal_factor_of_le`. -/
def Projection_averagingRectangle_equal_factor_of_leContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (R : ∀ i, Box (Fin (d i)))
    (_hR : R ∈ averagingRectangles I N G) (J : ∀ i, Box (Fin (d i)))
    (_hJ : J ∈ G) (_hRJ : ∀ i, R i ≤ J i),
    ∃ i, R i = J i

/-- Explicit type for `ReyZygmund.Projection.weaklyIncomparable_union_averagingRectangles`. -/
def Projection_weaklyIncomparable_union_averagingRectanglesContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (_hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (_hG : G ⊆ productDescendants I N)
    (_hweak : WeaklyIncomparable (G : Set (∀ i, Box (Fin (d i))))),
    WeaklyIncomparable
      ((G ∪ averagingRectangles I N G : Finset (∀ i, Box (Fin (d i)))) :
        Set (∀ i, Box (Fin (d i))))

/-- Explicit type for `ReyZygmund.Projection.weaklyIncomparable_union_preserves_averages`. -/
def Projection_weaklyIncomparable_union_preserves_averagesContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (_hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (_hG : G ⊆ productDescendants I N)
    (_hweak : WeaklyIncomparable (G : Set (∀ i, Box (Fin (d i)))))
    (R : ∀ i, Box (Fin (d i))) (_hR : R ∈ G ∪ averagingRectangles I N G),
    productAverageMap Finset.univ R * finiteProjectionMap I N G =
      productAverageMap Finset.univ R

/-- Explicit type for `ReyZygmund.Projection.finite_weakly_incomparable_representation`. -/
def Projection_finite_weakly_incomparable_representationContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (_hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (_hG : G ⊆ productDescendants I N)
    (_hweak : WeaklyIncomparable (G : Set (∀ i, Box (Fin (d i)))))
    (R : ∀ i, Box (Fin (d i))) (_hR : R ∈ G ∪ averagingRectangles I N G)
    (F : boundedMeasurableFunctions d) (_hf : ProductLeafConstant I N F.1)
    (_hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (x : ProductPoint d) (_hx : x ∈ productBox R),
    (productAverageMap Finset.univ R F).1 x =
      ∑ A ∈ ((Finset.univ : Finset (Fin m)).powerset.erase Finset.univ),
        (-1 : ℝ) ^ (m + 1 + A.card) *
          (productAverageMap A R (finiteProjectionMap I N G F)).1 x

/-- Explicit type for `ReyZygmund.finite_weakly_incomparable_representation_maximal`. -/
def finite_weakly_incomparable_representation_maximalContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (_hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (_hG : G ⊆ productDescendants I N)
    (_hweak : WeaklyIncomparable (G : Set (∀ i, Box (Fin (d i)))))
    (f : boundedMeasurableFunctions d) (_hf : ProductLeafConstant I N f.1)
    (_hs : ∀ x, x ∉ productBox I → f.1 x = 0)
    (_hpos : ∀ x ∈ productBox I, 0 ≤ f.1 x)
    (x : ProductPoint d),
    finiteFamilyMaximal (G ∪ averagingRectangles I N G) f x ≤
      (2 : ℝ) ^ m * ∑ j,
        finiteSignedPartialMaximal I N (Finset.univ.erase j)
          (finiteProjectionMap I N G f) x

/-- Explicit type for `ReyZygmund.finite_weakly_incomparable_maximal_to_square`. -/
def finite_weakly_incomparable_maximal_to_squareContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (_hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (_hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (_hG : G ⊆ productDescendants I N)
    (_hweak : WeaklyIncomparable (G : Set (∀ i, Box (Fin (d i)))))
    (f : boundedMeasurableFunctions d) (_hf : ProductLeafConstant I N f.1)
    (_hs : ∀ x, x ∉ productBox I → f.1 x = 0)
    (_hpos : ∀ x ∈ productBox I, 0 ≤ f.1 x)
    (p : ℝ) (_hp : 1 < p) (_hp3 : p ≤ (3 : ℝ) / 2),
    let C := (m : ℝ) * (2 : ℝ) ^ m *
      ((2 : ℝ) ^ (6 * (∑ i, d i) + 10) + (2 : ℝ) ^ (m - 1))
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal (G ∪ averagingRectangles I N G) f x) p) (1 / p) ≤
      C * (p / (p - 1)) ^ (m - 2) *
        Real.rpow (∫ x in productBox I, Real.rpow |f.1 x| p) (1 / p) +
      C * Real.rpow (∫ x in productBox I,
        Real.rpow (finiteComplementSquareFunction I N (finiteProjectionMap I N G f) x) p)
        (1 / p)

/-- Explicit type for `ReyZygmund.finite_weakly_incomparable_union_maximal_norm`. -/
def finite_weakly_incomparable_union_maximal_normContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (_hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (_hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (_hG : G ⊆ productDescendants I N)
    (_hweak : WeaklyIncomparable (G : Set (∀ i, Box (Fin (d i)))))
    (f : ProductPoint d → ℝ) (_hf : ProductLeafConstant I N f)
    (_hfpos : ∀ x ∈ productBox I, 0 < f x)
    (p : ℝ) (_hp : 1 < p) (_hp3 : p ≤ (3 : ℝ) / 2),
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal (G ∪ averagingRectangles I N G)
        (finiteInput I N f _hf) x) p) (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p)

/-- Explicit type for `ReyZygmund.finite_weakly_incomparable_maximal_norm`. -/
def finite_weakly_incomparable_maximal_normContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (_hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (_hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (_hG : G ⊆ productDescendants I N)
    (_hweak : WeaklyIncomparable (G : Set (∀ i, Box (Fin (d i)))))
    (f : ProductPoint d → ℝ) (_hf : ProductLeafConstant I N f)
    (_hfpos : ∀ x ∈ productBox I, 0 < f x)
    (p : ℝ) (_hp : 1 < p) (_hp3 : p ≤ (3 : ℝ) / 2),
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal G (finiteInput I N f _hf) x) p) (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p)

/-- Explicit type for `ReyZygmund.submitted_projected_weighted_square`. -/
def submitted_projected_weighted_squareContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (_hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (_hG : G ⊆ productDescendants I N)
    (f : ProductPoint d → ℝ) (_hf : ProductLeafConstant I N f)
    (_hfpos : ∀ x ∈ productBox I, 0 < f x)
    (p : ℝ) (_hp : 1 < p) (_hp2 : p ≤ 2),
    let F := finiteInput I N f _hf
    (∫ x in productBox I,
      (finiteComplementSquareFunction I N (finiteProjectionMap I N G F) x) ^ 2 /
        Real.rpow (finiteFamilyMaximal (averagingRectangles I N G) F x) (2 - p)) ≤
      ((m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)) *
        (p / (p - 1)) ^ (m - 1)) *
        ∫ x in productBox I, Real.rpow (f x) p

/-- Explicit type for `ReyZygmund.submitted_projected_holder_integral`. -/
def submitted_projected_holder_integralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (_hm : 0 < m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (_hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (_hG : G ⊆ productDescendants I N)
    (f : ProductPoint d → ℝ) (_hf : ProductLeafConstant I N f)
    (_hfpos : ∀ x ∈ productBox I, 0 < f x)
    (p : ℝ) (_hp : 1 < p) (_hp2 : p ≤ 2),
    let F := finiteInput I N f _hf
    let W := finiteComplementSquareFunction I N (finiteProjectionMap I N G F)
    let M := finiteFamilyMaximal (averagingRectangles I N G) F
    let K := (m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)) *
      (p / (p - 1)) ^ (m - 1)
    (∫ x in productBox I, Real.rpow (W x) p) ≤
      Real.rpow (K * ∫ x in productBox I, Real.rpow (f x) p) (p / 2) *
        Real.rpow (∫ x in productBox I, Real.rpow (M x) p) (1 - p / 2)

/-- Explicit type for `ReyZygmund.submitted_projected_holder_norm_variables`. -/
def submitted_projected_holder_norm_variablesContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (_hm : 0 < m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (_hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (_hG : G ⊆ productDescendants I N)
    (f : ProductPoint d → ℝ) (_hf : ProductLeafConstant I N f)
    (_hfpos : ∀ x ∈ productBox I, 0 < f x)
    (p : ℝ) (_hp : 1 < p) (_hp2 : p ≤ 2),
    let F := finiteInput I N f _hf
    let W := finiteComplementSquareFunction I N (finiteProjectionMap I N G F)
    let M := finiteFamilyMaximal (averagingRectangles I N G) F
    let X := Real.rpow (∫ x in productBox I, Real.rpow (M x) p) (1 / p)
    let Y := Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p)
    Real.rpow (∫ x in productBox I, Real.rpow (W x) p) (1 / p) ≤
      Real.sqrt ((m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1))) *
        Real.rpow (p / (p - 1)) (((m - 1 : ℕ) : ℝ) / 2) *
        Real.rpow Y (p / 2) * Real.rpow X (1 - p / 2)

/-- Explicit type for `ReyZygmund.Weighted.submitted_mixed_term_bound`. -/
def Weighted_submitted_mixed_term_boundContract : Prop :=
  ∀ (k : ℕ) (p A X Y : ℝ) (_hp : 1 < p)
    (_hA : 0 ≤ A) (_hX : 0 ≤ X) (_hY : 0 ≤ Y)
    (_h : X ≤ A * Real.rpow (p / (p - 1)) ((k : ℝ) / 2) *
      Real.rpow Y (p / 2) * Real.rpow X (1 - p / 2)),
    X ≤ Real.rpow A (2 / p) * Real.rpow (p / (p - 1)) ((k : ℝ) / p) * Y

/-- Explicit type for `ReyZygmund.Weighted.submitted_weighted_absorption`. -/
def Weighted_submitted_weighted_absorptionContract : Prop :=
  ∀ (m : ℕ) (_hm : 2 ≤ m)
    (p C X Y : ℝ) (_hp : 1 < p) (_hp3 : p ≤ (3 / 2 : ℝ))
    (_hC : 1 ≤ C) (_hX : 0 ≤ X) (_hY : 0 ≤ Y)
    (_h : X ≤ C * (p / (p - 1)) ^ (m - 2) * Y +
      C * Real.rpow (p / (p - 1)) (((m - 1 : ℕ) : ℝ) / 2) *
        Real.rpow Y (p / 2) * Real.rpow X (1 - p / 2)),
    X ≤ (2 * C) ^ 2 * (p / (p - 1)) ^ (m - 1) * Y

/-- Explicit type for `ReyZygmund.Projection.productDifferenceMap_eq_zero_of_leaf`. -/
def Projection_productDifferenceMap_eq_zero_of_leafContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (_hf : ProductLeafConstant I N F.1)
    (_hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (A : Finset (Fin m)) (K : ∀ i, Box (Fin (d i)))
    (i : Fin m) (_hi : i ∈ A) (_hKi : K i ∈ level (I i) (N i)),
    productDifferenceMap A K F = 0

/-- Explicit type for `ReyZygmund.Projection.finite_cross_projection_descendants`. -/
def Projection_finite_cross_projection_descendantsContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (_hd : ∀ i, 0 < d i) (G : Finset (∀ i, Box (Fin (d i))))
    (_hG : ∀ J ∈ G, ∀ i, J i ∈ descendants (I i) (N i))
    (f : ProductPoint d → ℝ) (_hf : ProductLeafConstant I N f)
    (j : Fin m) (K : ∀ i, Box (Fin (d i)))
    (_hK : ∀ i, i ≠ j → K i ∈ descendants (I i) (N i)),
    (productDifferenceMap (Finset.univ.erase j) K
      (finiteProjectionMap I N G (finiteInput I N f _hf))).1 =
        coordinateCrossAverage j (I j) (N j) (eligibleProjections j G K)
          (productDifferenceMap (Finset.univ.erase j) K (finiteInput I N f _hf)).1

/-- Explicit type for `ReyZygmund.Projection.common_cutoff_leaves_iff`. -/
def Projection_common_cutoff_leaves_iffContract : Prop :=
  ∀ {e : ℕ}
    (D : DyadicGrid e) (n k : ℤ) (I Q : Box (Fin e))
    (_hI : I ∈ D.cubes n) (_hnk : n ≤ k),
    Q ∈ leaves I (k - n).toNat ↔ Q ∈ D.cubes k ∧ Q ≤ I

/-- Explicit type for `ReyZygmund.Projection.common_cutoff_productLeaves_iff`. -/
def Projection_common_cutoff_productLeaves_iffContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (_hI : ∀ i, I i ∈ (D i).cubes (n i))
    (_hnk : ∀ i, n i ≤ k) (R : ∀ i, Box (Fin (d i))),
    R ∈ productLeaves I (fun i => (k - n i).toNat) ↔
      (∀ i, R i ∈ (D i).cubes k) ∧ productBox R ⊆ productBox I

/-- Explicit type for `ReyZygmund.Projection.common_cutoff_family_finite`. -/
def Projection_common_cutoff_family_finiteContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (_hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (_hI : ∀ i, I i ∈ (D i).cubes (n i))
    (_hnk : ∀ i, n i ≤ k) (G : Set (∀ i, Box (Fin (d i))))
    (_hG : ∀ R ∈ G, R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
      ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u),
    G.Finite

/-- Explicit type for `ReyZygmund.Projection.source_grid_projection`. -/
def Projection_source_grid_projectionContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (_hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (_hI : ∀ i, I i ∈ (D i).cubes (n i))
    (_hnk : ∀ i, n i ≤ k) (G : Finset (∀ i, Box (Fin (d i))))
    (_hG : ∀ R ∈ G, R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
      ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u)
    (f : ProductPoint d → ℝ) (_hs : ∀ x, x ∉ productBox I → f x = 0)
    (_hf : ∀ R, (R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
      ∀ i u, (R i).upper u - (R i).lower u = (2 : ℝ) ^ (-k)) →
      ∀ x ∈ productBox R, ∀ y ∈ productBox R, f x = f y),
    let N := fun i => (k - n i).toNat
    ∃ _hleaf : ProductLeafConstant I N f,
      let u := finiteInput I N f _hleaf
      u.1 = f ∧
      (Function.support (fun L : {L : ∀ i, Box (Fin (d i)) //
          L ∈ gridRectangles D ∧ ∃ J ∈ G, productBox L ⊆ productBox J} =>
        rawProductDifference L.1 f)).Finite ∧
      ((finiteProjectionMap I N G u).1 = f -
        ∑' L : {L : ∀ i, Box (Fin (d i)) //
          L ∈ gridRectangles D ∧ ∃ J ∈ G, productBox L ⊆ productBox J},
          rawProductDifference L.1 f) ∧
      ProductLeafConstant I N (finiteProjectionMap I N G u).1 ∧
      ∀ x, x ∉ productBox I → (finiteProjectionMap I N G u).1 x = 0

/-- Explicit type for `ReyZygmund.Geometry.sliceFamily_weaklyIncomparable`. -/
def Geometry_sliceFamily_weaklyIncomparableContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (_hn : 0 < n) (D : ∀ i, DyadicGrid (d i))
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) (_hphi : Monotone phi)
    (G : Set (∀ i, Box (Fin (d i)))) (_hG : G ⊆ roundedGridRectangles D phi)
    (_hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (t : Fin (d (Fin.last n)) → ℝ),
    WeaklyIncomparable (sliceFamily G t)

/-- Explicit type for `ReyZygmund.Geometry.sliceFamily_existsUnique`. -/
def Geometry_sliceFamily_existsUniqueContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (D : ∀ i, DyadicGrid (d i)) (G : Set (∀ i, Box (Fin (d i))))
    (_hG : G ⊆ gridRectangles D)
    (_hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (t : Fin (d (Fin.last n)) → ℝ)
    {P : ∀ i : Fin n, Box (Fin (d i.castSucc))} (_hP : P ∈ sliceFamily G t),
    ∃! R, R ∈ G ∧ t ∈ R (Fin.last n) ∧ initialProjection R = P

/-- Explicit type for `ReyZygmund.Geometry.overlap_splitLast_symm`. -/
def Geometry_overlap_splitLast_symmContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (D : ∀ i, DyadicGrid (d i)) (G : Set (∀ i, Box (Fin (d i))))
    (_hG : G ⊆ gridRectangles D)
    (_hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (y : Fin (∑ i : Fin n, d i.castSucc) → ℝ) (t : Fin (d (Fin.last n)) → ℝ),
    ReyZygmund.Overlap.overlap G ((splitLastCoordinates d).symm (y, t)) = ReyZygmund.Overlap.overlap (sliceFamily G t) y

end ReyZygmundVerification.SubmittedAlignment
