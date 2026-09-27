import ReyZygmund.Overlap.EndpointMoments

/-! Finite sparse-moment propositions under conditional maximal growth. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry ReyZygmund.Overlap

def finiteEndpointSparseOverlapIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i))))
    (eta : ℝ), 0 < eta →
    ∀ E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ),
      (∀ R ∈ G, MeasurableSet (E R)) →
      (∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) →
      Set.Pairwise (G : Set (∀ i, Box (Fin (d i))))
        (fun R S => Disjoint (E R) (E S)) →
      (∀ R ∈ G, ENNReal.ofReal eta *
        volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤ volume (E R)) →
      ∀ (k : ℕ) (C : ℝ), 0 < C →
      (∀ f : (Fin (∑ i, d i) → ℝ) → ℝ,
        LocallyIntegrable f volume → Measurable f → (∀ x, 0 ≤ f x) →
        ∀ p : ℝ, 1 < p → p ≤ 2 →
          (∫⁻ x, ENNReal.ofReal (Real.rpow
            ((euclideanFamilyMaximal (G : Set _) f x).toReal) p)) ≤
            ENNReal.ofReal (Real.rpow (C / (p - 1) ^ k) p) *
              ∫⁻ x, ENNReal.ofReal (Real.rpow (f x) p)) →
      ∀ q : ℝ, 2 ≤ q →
        Real.rpow (∫ x, Real.rpow (finiteOverlap G x) q) (1 / q) ≤
          C * eta⁻¹ * q ^ k * Real.rpow (volume.real (finiteShadow G)) (1 / q)

def finiteEndpointSparseOverlapLIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i))))
    (eta : ℝ), 0 < eta →
    ∀ E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ),
      (∀ R ∈ G, MeasurableSet (E R)) →
      (∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) →
      Set.Pairwise (G : Set (∀ i, Box (Fin (d i))))
        (fun R S => Disjoint (E R) (E S)) →
      (∀ R ∈ G, ENNReal.ofReal eta *
        volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤ volume (E R)) →
      ∀ (k : ℕ) (C : ℝ), 0 < C →
      (∀ f : (Fin (∑ i, d i) → ℝ) → ℝ,
        LocallyIntegrable f volume → Measurable f → (∀ x, 0 ≤ f x) →
        ∀ p : ℝ, 1 < p → p ≤ 2 →
          (∫⁻ x, ENNReal.ofReal (Real.rpow
            ((euclideanFamilyMaximal (G : Set _) f x).toReal) p)) ≤
            ENNReal.ofReal (Real.rpow (C / (p - 1) ^ k) p) *
              ∫⁻ x, ENNReal.ofReal (Real.rpow (f x) p)) →
      ∀ q : ℝ, 2 ≤ q →
        (∫⁻ x, (ENNReal.ofReal (finiteOverlap G x)) ^ q) ≤
          (ENNReal.ofReal (C * eta⁻¹ * q ^ k)) ^ q * volume (finiteShadow G)

end ReyZygmundVerification
