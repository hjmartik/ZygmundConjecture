import ReyZygmund.Geometry.CoordinateFibreOperators
import ReyZygmund.Geometry.FibreIntegration

/-! Expected finite fibre identities and integration statements. -/

open BoxIntegral MeasureTheory
open scoped BigOperators
open ReyZygmund ReyZygmund.Geometry ReyZygmund.Projection

namespace ReyZygmundVerification

def coordinateFibreLeafContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin (n + 1) → ℕ)
    (f : ProductPoint d → ℝ), ProductLeafConstant I N f →
  ∀ (j : Fin (n + 1)) (t : Fin (d j) → ℝ), t ∈ I j →
    ProductLeafConstant (fun i => I (j.succAbove i)) (fun i => N (j.succAbove i))
      (fun y => f (j.insertNth t y))

def coordinateFibreSupportContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (I : ∀ i, Box (Fin (d i))) (f : ProductPoint d → ℝ),
    (∀ x, x ∉ productBox I → f x = 0) →
  ∀ (j : Fin (n + 1)) (t : Fin (d j) → ℝ)
    (y : ProductPoint (fun i => d (j.succAbove i))),
    y ∉ productBox (fun i => I (j.succAbove i)) → f (j.insertNth t y) = 0

def coordinateFibreDifferenceSumContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin (n + 1) → ℕ)
    (j : Fin (n + 1)) (t : Fin (d j) → ℝ) (F : boundedMeasurableFunctions d),
    coordinateFibreMap j t
        (∑ Q ∈ partialInterior I N (Finset.univ.erase j),
          productDifferenceMap (Finset.univ.erase j) Q F) =
      ∑ Q ∈ productInterior (fun i => I (j.succAbove i)) (fun i => N (j.succAbove i)),
        productDifferenceMap Finset.univ Q (coordinateFibreMap j t F)

def coordinateFibreSquareContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin (n + 1) → ℕ)
    (j : Fin (n + 1)) (t : Fin (d j) → ℝ) (F : boundedMeasurableFunctions d)
    (y : ProductPoint (fun i => d (j.succAbove i))),
    finiteSquareFunction I N (Finset.univ.erase j) F (j.insertNth t y) =
      finiteSquareFunction (fun i => I (j.succAbove i)) (fun i => N (j.succAbove i))
        Finset.univ (coordinateFibreMap j t F) y

def coordinateFibreSignedMaximalContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin (n + 1) → ℕ)
    (j : Fin (n + 1)) (t : Fin (d j) → ℝ) (F : boundedMeasurableFunctions d)
    (y : ProductPoint (fun i => d (j.succAbove i))),
    finiteSignedPartialMaximal I N (Finset.univ.erase j) F (j.insertNth t y) =
      finiteSignedProductMaximal (fun i => I (j.succAbove i)) (fun i => N (j.succAbove i))
        (coordinateFibreMap j t F) y

def coordinateFibreIntegralContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin (n + 1) → ℕ)
    (H : ProductPoint d → ℝ), ProductLeafConstant I N H →
  ∀ (j : Fin (n + 1)),
    (∫ x in productBox I, H x) =
      ∫ t in (I j : Set (Fin (d j) → ℝ)),
        ∫ y in productBox (fun i => I (j.succAbove i)), H (j.insertNth t y)

def coordinateFibreIntegralIntegrabilityContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin (n + 1) → ℕ)
    (H : ProductPoint d → ℝ), ProductLeafConstant I N H →
  ∀ (j : Fin (n + 1)),
    IntegrableOn
      (fun t => ∫ y in productBox (fun i => I (j.succAbove i)), H (j.insertNth t y))
      (I j : Set (Fin (d j) → ℝ)) volume

end ReyZygmundVerification
