import ReyZygmund.Maximal.GlobalCoordinateDefs
import ReyZygmund.Maximal.Countable
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

/-! Propositions for the full-grid coordinate composition. No candidate
coordinate proof module is imported. All powers of extended values are real
powers; the final signed-input statement imposes only MemLp. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmundVerification

open ReyZygmund ReyZygmund.Geometry

def coordinateGridAverageMeasurableContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (j : Fin m) (Q : Box (Fin (d j)))
    (F : ProductPoint d → ℝ≥0∞), Measurable F →
      Measurable (coordinateGridAverage j Q F)

def coordinateGridMaximalMeasurableContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, DyadicGrid (d i)) (j : Fin m)
    (F : ProductPoint d → ℝ≥0∞), Measurable F →
      Measurable (coordinateGridMaximal D j F)

def coordinateGridMaximalMonotoneContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, DyadicGrid (d i)) (j : Fin m)
    (F G : ProductPoint d → ℝ≥0∞), F ≤ G →
      coordinateGridMaximal D j F ≤ coordinateGridMaximal D j G

def coordinateGridMaximalUpdateContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, DyadicGrid (d i)) (j : Fin m)
    (F : ProductPoint d → ℝ≥0∞) (x : ProductPoint d) (y : Fin (d j) → ℝ),
    coordinateGridMaximal D j F (Function.update x j y) =
      ⨆ Q : {Q : Box (Fin (d j)) | ∃ n : ℤ, Q ∈ (D j).cubes n},
        (Q.1 : Set (Fin (d j) → ℝ)).indicator
          (fun _ => (volume (Q.1 : Set (Fin (d j) → ℝ)))⁻¹ *
            ∫⁻ z in (Q.1 : Set (Fin (d j) → ℝ)), F (Function.update x j z)) y

def coordinateGridMaximalAeCongrContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, DyadicGrid (d i)) (j : Fin m)
    (F G : ProductPoint d → ℝ≥0∞), F =ᵐ[volume] G →
      coordinateGridMaximal D j F =ᵐ[volume] coordinateGridMaximal D j G

def coordinateGridMaximalAEMeasurableContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, DyadicGrid (d i)) (j : Fin m)
    (F : ProductPoint d → ℝ≥0∞), AEMeasurable F volume →
      AEMeasurable (coordinateGridMaximal D j F) volume

def coordinateGridMaximalPowerIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, DyadicGrid (d i)) (j : Fin m),
    0 < d j → ∀ (F : ProductPoint d → ℝ≥0∞), Measurable F →
      ∀ p : ℝ, 1 < p →
        (∫⁻ x, (coordinateGridMaximal D j F x) ^ p) ≤
          (ENNReal.ofReal (p / (p - 1))) ^ p * ∫⁻ x, (F x) ^ p

def iteratedGridMaximalMeasurableContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, DyadicGrid (d i))
    (F : ProductPoint d → ℝ≥0∞), Measurable F →
      Measurable (iteratedGridMaximal D F)

def productAverageIteratedGridMaximalContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, DyadicGrid (d i))
    (F : ProductPoint d → ℝ≥0∞), Measurable F →
      ∀ Q : ∀ i, Box (Fin (d i)), Q ∈ gridRectangles D →
        ∀ x : ProductPoint d,
          (productBox Q).indicator
            (fun _ => (volume (productBox Q))⁻¹ * ∫⁻ y in productBox Q, F y) x ≤
              iteratedGridMaximal D F x

def iteratedGridMaximalPowerIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, DyadicGrid (d i)),
    (∀ i, 0 < d i) → ∀ F : ProductPoint d → ℝ≥0∞, Measurable F →
      ∀ p : ℝ, 1 < p →
        (∫⁻ x, (iteratedGridMaximal D F x) ^ p) ≤
          (ENNReal.ofReal ((p / (p - 1)) ^ m)) ^ p * ∫⁻ x, (F x) ^ p

def ordinaryCoordinateCompositionContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, DyadicGrid (d i)),
    (∀ i, 0 < d i) → ∀ (f : ProductPoint d → ℝ) (p : ℝ), 1 < p →
      MemLp f (ENNReal.ofReal p) volume →
      let T := iteratedGridMaximal D (fun x => ENNReal.ofReal |f x|)
      AEMeasurable T volume ∧
      (∀ᵐ x ∂volume, T x < ∞) ∧
      MemLp (fun x => (T x).toReal) (ENNReal.ofReal p) volume ∧
      (∀ᵐ x ∂volume, familyMaximal (gridRectangles D) f x ≤ T x) ∧
      eLpNorm (fun x => (familyMaximal (gridRectangles D) f x).toReal)
          (ENNReal.ofReal p) volume ≤
        eLpNorm (fun x => (T x).toReal) (ENNReal.ofReal p) volume ∧
      eLpNorm (fun x => (T x).toReal) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal ((p / (p - 1)) ^ m) * eLpNorm f (ENNReal.ofReal p) volume

end ReyZygmundVerification
