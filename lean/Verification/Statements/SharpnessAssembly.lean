import ReyZygmund.Continuous.DyadicExtension
import ReyZygmund.Overlap.Finite

/-!
# Explicit propositions for the ordinary-coordinate sharpness assembly

These bodies use only the existing geometric and finite-overlap definitions.
Neither the candidate construction, lower-bound proof, nor main solution is
imported. The independent main challenge remains unchanged.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmundVerification

open ReyZygmund.Geometry ReyZygmund.Continuous ReyZygmund.Overlap

def sharpVolumeFlattenSetContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (A : Set (ProductPoint d)),
    volume ((flattenCoordinates d).symm ⁻¹' A) = volume A

def sharpFiniteShadowFlattenContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i)))),
    (flattenCoordinates d) ⁻¹' finiteShadow G = ⋃ R ∈ G, productBox R

def sharpFiniteOverlapFlattenContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i))))
    (x : ProductPoint d),
    finiteOverlap G (flattenCoordinates d x) =
      ∑ R ∈ G, (productBox R).indicator (fun _ => (1 : ℝ)) x

def sharpUnitRootVolumeContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, DyadicGrid (d i))
    (Q : ∀ i, Box (Fin (d i))),
    (∀ i, Q i ∈ (D i).cubes 0) → volume (productBox Q) = 1

def sharpFlatConstructionContract : Prop :=
  ∀ (n N s : ℕ), 2 ≤ N → 1 ≤ s →
    ∀ (d : Fin (n + 3) → ℕ), (∀ j, 0 < d j) →
      ∀ (D : ∀ j, DyadicGrid (d j)),
        ∃ G : Finset (∀ j, Box (Fin (d j))),
          ∃ E : (∀ j, Box (Fin (d j))) → Set (Fin (∑ j, d j) → ℝ),
            ∃ L : Set (Fin (∑ j, d j) → ℝ),
          (↑G : Set (∀ j, Box (Fin (d j)))) ⊆
            dyadicPhiRectangles D (fun k : Fin (n + 2) → ℤ => ∑ i, k i) ∧
          (∀ R ∈ G, ∀ S ∈ G,
            (flatProductBox R : Set (Fin (∑ j, d j) → ℝ)) ⊆ flatProductBox S → R = S) ∧
          volume (finiteShadow G) = 1 ∧
          (∀ R ∈ G, MeasurableSet (E R) ∧ E R ⊆ flatProductBox R ∧
            volume.real (E R) = (1 - (2 : ℝ) ^ (-(s : ℤ))) ^ (n + 2) *
              volume.real (flatProductBox R : Set (Fin (∑ j, d j) → ℝ))) ∧
          Set.PairwiseDisjoint (↑G : Set (∀ j, Box (Fin (d j)))) E ∧
          MeasurableSet L ∧ L ⊆ finiteShadow G ∧
          (∀ x ∈ L, finiteOverlap G x = (N : ℝ) ^ (n + 2)) ∧
          volume.real L = ((2 : ℝ) ^ (-(s : ℤ))) ^ ((n + 2) * (N - 1))

def sharpFiniteExponentialLowerContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (G : Finset (∀ i, Box (Fin (d i))))
    (L : Set (Fin (∑ i, d i) → ℝ)),
    MeasurableSet L → L ⊆ finiteShadow G →
      ∀ M c beta : ℝ, (∀ x ∈ L, finiteOverlap G x = M) → 0 < c → 0 < beta →
        volume.real L * (Real.exp (c * Real.rpow M beta) - 1) ≤
          ∫ x in finiteShadow G,
            Real.exp (c * Real.rpow (finiteOverlap G x) beta) - 1 ∂volume

end ReyZygmundVerification
