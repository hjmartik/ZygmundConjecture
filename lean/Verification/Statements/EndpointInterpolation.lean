import ReyZygmund.Maximal.EndpointFinite

/-! Propositions for the conditional endpoint interpolation helpers.

The weak hypotheses below apply to every locally integrable input. These are
not the bounded-input-only endpoint-to-overlap bridge or a sparse conclusion.
-/

open BoxIntegral MeasureTheory Set
open scoped BigOperators Classical ENNReal

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry

def euclideanMaximalTruncationLevelsetContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ),
    LocallyIntegrable f volume → Measurable f → (∀ x, 0 ≤ f x) →
    ∀ lam : ℝ, 0 < lam →
      {x | ENNReal.ofReal lam < euclideanFamilyMaximal G f x} ⊆
        {x | ENNReal.ofReal (lam / 2) < euclideanFamilyMaximal G
          ({y | lam / 2 < f y}.indicator f) x}

def euclideanEndpointTruncatedDistributionContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Set (∀ i, Box (Fin (d i))))
    (k : ℕ) (A : ℝ), 0 ≤ A →
    (∀ g : (Fin (∑ i, d i) → ℝ) → ℝ,
      LocallyIntegrable g volume → ∀ t : ℝ, 0 < t →
        volume {x | ENNReal.ofReal t < euclideanFamilyMaximal G g x} ≤
          ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
            (|g x| / t * (Real.log (Real.exp 1 + |g x| / t)) ^ k)) →
    ∀ f : (Fin (∑ i, d i) → ℝ) → ℝ,
      LocallyIntegrable f volume → Measurable f → (∀ x, 0 ≤ f x) →
      ∀ lam : ℝ, 0 < lam →
        volume {x | ENNReal.ofReal lam < euclideanFamilyMaximal G f x} ≤
          ENNReal.ofReal (2 * A / lam) *
            ∫⁻ x in {x | lam / 2 < f x}, ENNReal.ofReal
              (f x * (Real.log (Real.exp 1 + 2 * f x / lam)) ^ k)

def endpointTruncatedMomentSwapContract : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (mu : Measure X) [SFinite mu]
    (f : X → ℝ), Measurable f → (∀ x, 0 ≤ f x) →
    ∀ (k : ℕ) (p A : ℝ), 0 ≤ A →
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.rpow t (p - 1)) *
        (ENNReal.ofReal (2 * A / t) *
          ∫⁻ x in {x | t / 2 < f x}, ENNReal.ofReal
            (f x * (Real.log (Real.exp 1 + 2 * f x / t)) ^ k) ∂mu)) =
        ENNReal.ofReal (2 * A) * ∫⁻ x, ENNReal.ofReal (f x) *
          ∫⁻ t in Ioo (0 : ℝ) (2 * f x), ENNReal.ofReal
            (Real.rpow t (p - 2) *
              (Real.log (Real.exp 1 + 2 * f x / t)) ^ k) ∂volume ∂mu

def lintegralRpowLeEndpointKernelContract : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (mu : Measure X) [SFinite mu]
    (f F : X → ℝ), Measurable f → (∀ x, 0 ≤ f x) →
    Measurable F → (∀ x, 0 ≤ F x) →
    ∀ (k : ℕ) (p A : ℝ), 0 < p → 0 ≤ A →
    (∀ t : ℝ, 0 < t →
      mu {x | t < F x} ≤ ENNReal.ofReal (2 * A / t) *
        ∫⁻ x in {x | t / 2 < f x}, ENNReal.ofReal
          (f x * (Real.log (Real.exp 1 + 2 * f x / t)) ^ k) ∂mu) →
    (∫⁻ x, ENNReal.ofReal (Real.rpow (F x) p) ∂mu) ≤
      ENNReal.ofReal (2 * A * p) * ∫⁻ x, ENNReal.ofReal (f x) *
        ∫⁻ t in Ioo (0 : ℝ) (2 * f x), ENNReal.ofReal
          (Real.rpow t (p - 2) *
            (Real.log (Real.exp 1 + 2 * f x / t)) ^ k) ∂volume ∂mu

def endpointDistributionStrongPowerContract : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (mu : Measure X) [SFinite mu]
    (f F : X → ℝ), Measurable f → (∀ x, 0 ≤ f x) →
    Measurable F → (∀ x, 0 ≤ F x) →
    ∀ (k : ℕ) (p A : ℝ), 1 < p → p ≤ 2 → 0 ≤ A →
    (∀ t : ℝ, 0 < t →
      mu {x | t < F x} ≤ ENNReal.ofReal (2 * A / t) *
        ∫⁻ x in {x | t / 2 < f x}, ENNReal.ofReal
          (f x * (Real.log (Real.exp 1 + 2 * f x / t)) ^ k) ∂mu) →
    (∫⁻ x, ENNReal.ofReal (Real.rpow (F x) p) ∂mu) ≤
      ENNReal.ofReal (8 * A * Real.exp 2 * (k.factorial : ℝ) /
        (p - 1) ^ (k + 1)) *
          ∫⁻ x, ENNReal.ofReal (Real.rpow (f x) p) ∂mu

def finiteEndpointMaximalPowerContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i))))
    (k : ℕ) (A : ℝ), 0 ≤ A →
    (∀ g : (Fin (∑ i, d i) → ℝ) → ℝ,
      LocallyIntegrable g volume → ∀ t : ℝ, 0 < t →
        volume {x | ENNReal.ofReal t < euclideanFamilyMaximal (G : Set _) g x} ≤
          ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
            (|g x| / t * (Real.log (Real.exp 1 + |g x| / t)) ^ k)) →
    ∀ f : (Fin (∑ i, d i) → ℝ) → ℝ,
      LocallyIntegrable f volume → Measurable f → (∀ x, 0 ≤ f x) →
      ∀ p : ℝ, 1 < p → p ≤ 2 →
        (∫⁻ x, ENNReal.ofReal
          (Real.rpow ((euclideanFamilyMaximal (G : Set _) f x).toReal) p)) ≤
          ENNReal.ofReal (8 * A * Real.exp 2 * (k.factorial : ℝ) /
            (p - 1) ^ (k + 1)) *
              ∫⁻ x, ENNReal.ofReal (Real.rpow (f x) p)

def finiteEndpointMaximalPowerUniformContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i))))
    (k : ℕ) (A : ℝ), 0 ≤ A →
    (∀ g : (Fin (∑ i, d i) → ℝ) → ℝ,
      LocallyIntegrable g volume → ∀ t : ℝ, 0 < t →
        volume {x | ENNReal.ofReal t < euclideanFamilyMaximal (G : Set _) g x} ≤
          ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
            (|g x| / t * (Real.log (Real.exp 1 + |g x| / t)) ^ k)) →
    ∀ f : (Fin (∑ i, d i) → ℝ) → ℝ,
      LocallyIntegrable f volume → Measurable f → (∀ x, 0 ≤ f x) →
      ∀ p : ℝ, 1 < p → p ≤ 2 →
        (∫⁻ x, ENNReal.ofReal
          (Real.rpow ((euclideanFamilyMaximal (G : Set _) f x).toReal) p)) ≤
          ENNReal.ofReal (Real.rpow
            (max 1 (8 * A * Real.exp 2 * (k.factorial : ℝ)) /
              (p - 1) ^ (k + 1)) p) *
                ∫⁻ x, ENNReal.ofReal (Real.rpow (f x) p)

end ReyZygmundVerification
