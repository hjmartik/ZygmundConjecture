import ReyZygmund.Geometry.GlobalDifferences
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Independent contracts for the global signed-square assembly.
No candidate limit, forest, square-estimate or Main module is imported.
The finite square on the first right-hand side is expanded inline. -/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmundVerification

open ReyZygmund.Geometry

def signedGridSquareIntegralContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, DyadicGrid (d i)),
    (∀ i, 0 < d i) →
    ∀ (H : Finset (∀ i, Box (Fin (d i)))),
      (↑H : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D →
      ∀ F : boundedMeasurableFunctions d,
        F.1 = (fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x) →
        ∀ p : ℝ, 1 ≤ p → p ≤ (3 : ℝ) / 2 →
          (∫⁻ x, (signedGridMaximal D F.1 x) ^ p) ≤
            ENNReal.ofReal ((2 : ℝ) ^ (6 * (∑ i, d i) + 10)) *
              ENNReal.ofReal (∫ x, Real.rpow
                (Real.sqrt (∑ Q ∈ H, (rawProductDifference Q F.1 x) ^ 2)) p)

def fullGridSquareEstimateContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, DyadicGrid (d i)),
    (∀ i, 0 < d i) →
    ∀ (H : Finset (∀ i, Box (Fin (d i)))),
      (↑H : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D →
      ∀ g : ProductPoint d → ℝ,
        (g =ᵐ[volume] fun x => ∑ Q ∈ H, rawProductDifference Q g x) →
        ∀ p : ℝ, 1 ≤ p → p ≤ (3 : ℝ) / 2 →
          Integrable g volume ∧
          Measurable (signedGridMaximal D g) ∧
          Measurable (fullGridSquare D g) ∧
          (∀ᵐ x ∂volume, signedGridMaximal D g x < ∞) ∧
          (∀ᵐ x ∂volume, fullGridSquare D g x < ∞) ∧
          MemLp (fun x => (signedGridMaximal D g x).toReal)
            (ENNReal.ofReal p) volume ∧
          MemLp (fun x => (fullGridSquare D g x).toReal)
            (ENNReal.ofReal p) volume ∧
          eLpNorm (fun x => (signedGridMaximal D g x).toReal)
              (ENNReal.ofReal p) volume ≤
            ENNReal.ofReal ((2 : ℝ) ^ (6 * (∑ i, d i) + 10)) *
              eLpNorm (fun x => (fullGridSquare D g x).toReal)
                (ENNReal.ofReal p) volume

end ReyZygmundVerification
