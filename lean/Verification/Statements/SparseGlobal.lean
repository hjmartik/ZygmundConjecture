import ReyZygmund.Overlap.Global

/-! Explicit countable sparse-overlap moment propositions. -/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry ReyZygmund.Overlap

def weakerSparseOverlapIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (_hm : 2 ≤ m) (_hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (_hG : G ⊆ gridRectangles D)
    (_hweak : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i)
    (eta : ℝ) (_heta : 0 < eta)
    (E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ))
    (_hEmeas : ∀ R ∈ G, MeasurableSet (E R))
    (_hEsub : ∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)))
    (_hEdis : Set.Pairwise G (fun R S => Disjoint (E R) (E S)))
    (_hEmass : ∀ R ∈ G, ENNReal.ofReal eta *
      volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤ volume (E R))
    (q : ℝ) (_hq : 2 ≤ q),
    (∫⁻ x, (overlap G x) ^ q) ≤
      (ENNReal.ofReal ((maximalDimensionConstant d + 3) * eta⁻¹ * q ^ (m - 1))) ^ q *
        volume (shadow G)

def weakerSparseOverlapFiniteAEContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (_hm : 2 ≤ m) (_hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (_hG : G ⊆ gridRectangles D)
    (_hweak : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i)
    (eta : ℝ) (_heta : 0 < eta)
    (E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ))
    (_hEmeas : ∀ R ∈ G, MeasurableSet (E R))
    (_hEsub : ∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)))
    (_hEdis : Set.Pairwise G (fun R S => Disjoint (E R) (E S)))
    (_hEmass : ∀ R ∈ G, ENNReal.ofReal eta *
      volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤ volume (E R))
    (_hshadow : volume (shadow G) < ∞),
    ∀ᵐ x ∂volume, overlap G x < ∞

def weakerSparseOverlapNormContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (_hm : 2 ≤ m) (_hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (_hG : G ⊆ gridRectangles D)
    (_hweak : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i)
    (eta : ℝ) (_heta : 0 < eta)
    (E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ))
    (_hEmeas : ∀ R ∈ G, MeasurableSet (E R))
    (_hEsub : ∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)))
    (_hEdis : Set.Pairwise G (fun R S => Disjoint (E R) (E S)))
    (_hEmass : ∀ R ∈ G, ENNReal.ofReal eta *
      volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤ volume (E R))
    (_hshadow : volume (shadow G) < ∞) (q : ℝ) (_hq : 2 ≤ q),
    eLpNorm (fun x => (overlap G x).toReal) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal ((maximalDimensionConstant d + 3) * eta⁻¹ * q ^ (m - 1)) *
        (volume (shadow G)) ^ (1 / q)

end ReyZygmundVerification
