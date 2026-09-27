import ReyZygmund.Maximal.SignedFinite

/-! Expected statements for directed limits of signed rectangle means.
No maximal estimate is supplied by these conditional limit propositions. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry

def finiteSignedGridMaximalMeasurableContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (H : Finset (∀ i, Box (Fin (d i))))
    (f : ProductPoint d → ℝ), Measurable (finiteSignedGridMaximal H f)

def finiteSignedGridMaximalMonotoneContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (H K : Finset (∀ i, Box (Fin (d i)))),
    H ⊆ K → ∀ (f : ProductPoint d → ℝ) (x : ProductPoint d),
      finiteSignedGridMaximal H f x ≤ finiteSignedGridMaximal K f x

def signedGridMaximalFiniteSupremumContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (D : ∀ i, DyadicGrid (d i))
    (f : ProductPoint d → ℝ) (x : ProductPoint d),
      signedGridMaximal D f x = ⨆ H : Finset (gridRectangles D),
        finiteSignedGridMaximal (H.image Subtype.val) f x

def signedGridMaximalPowerIntegralSupremumContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (D : ∀ i, DyadicGrid (d i))
    (f : ProductPoint d → ℝ) (p : ℝ), 0 < p →
      (∫⁻ x, (signedGridMaximal D f x) ^ p) =
        ⨆ H : Finset (gridRectangles D), ∫⁻ x,
          (finiteSignedGridMaximal (H.image Subtype.val) f x) ^ p

def signedGridMaximalPowerIntegralBoundContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (D : ∀ i, DyadicGrid (d i))
    (f : ProductPoint d → ℝ) (p : ℝ), 0 < p → ∀ (C : ℝ≥0∞),
      (∀ H : Finset (gridRectangles D),
        (∫⁻ x, (finiteSignedGridMaximal (H.image Subtype.val) f x) ^ p) ≤ C) →
      (∫⁻ x, (signedGridMaximal D f x) ^ p) ≤ C

def signedGridMaximalAeFiniteContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (D : ∀ i, DyadicGrid (d i))
    (f : ProductPoint d → ℝ) (p : ℝ), 0 < p →
      (∫⁻ x, (signedGridMaximal D f x) ^ p) < ∞ →
      ∀ᵐ x ∂volume, signedGridMaximal D f x < ∞

def signedGridMaximalMemLpContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (D : ∀ i, DyadicGrid (d i))
    (f : ProductPoint d → ℝ) (p : ℝ), 0 < p →
      (∫⁻ x, (signedGridMaximal D f x) ^ p) < ∞ →
      MemLp (fun x => (signedGridMaximal D f x).toReal) (ENNReal.ofReal p) volume

end ReyZygmundVerification
