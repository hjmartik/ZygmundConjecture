import ReyZygmund.Geometry.PartialIndices
import ReyZygmund.Geometry.ProductClosure
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Finite partial square functions

Fix unused coordinates at the top cubes, so each partial difference index is
counted once. The complement square function is the finite expression `W F` in the
paper.

-/

open BoxIntegral
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

noncomputable def finiteSquareFunction
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (A : Finset (Fin m))
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) : ℝ :=
  Real.sqrt (∑ Q ∈ partialInterior I N A, ((productDifferenceMap A Q F).1 x) ^ 2)

noncomputable def finiteComplementSquareFunction
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) : ℝ :=
  Real.sqrt (∑ j : Fin m, ∑ Q ∈ partialInterior I N (Finset.univ.erase j),
    ((productDifferenceMap (Finset.univ.erase j) Q F).1 x) ^ 2)

theorem finiteSquareFunction_sq
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (A : Finset (Fin m))
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) :
    (finiteSquareFunction I N A F x) ^ 2 =
      ∑ Q ∈ partialInterior I N A, ((productDifferenceMap A Q F).1 x) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem finiteSquareFunction_empty
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) :
    finiteSquareFunction I N ∅ F x = |F.1 x| := by
  simp [finiteSquareFunction, Real.sqrt_sq_eq_abs]

theorem finiteComplementSquareFunction_sq
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) :
    (finiteComplementSquareFunction I N F x) ^ 2 =
      ∑ j : Fin m, ∑ Q ∈ partialInterior I N (Finset.univ.erase j),
        ((productDifferenceMap (Finset.univ.erase j) Q F).1 x) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem finiteComplementSquareFunction_eq_partial
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) :
    finiteComplementSquareFunction I N F x =
      Real.sqrt (∑ j : Fin m, (finiteSquareFunction I N (Finset.univ.erase j) F x) ^ 2) := by
  simp only [finiteSquareFunction_sq, finiteComplementSquareFunction]

theorem productLeafConstant_finiteSquareFunction
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (A : Finset (Fin m))
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) :
    ProductLeafConstant I N (finiteSquareFunction I N A F) := by
  intro P hP x hx y hy
  apply congrArg Real.sqrt
  apply Finset.sum_congr rfl
  intro Q hQ
  have h := (productDifferenceMap_productStep_closure I N F hf hs A Q
    (fun i hi => partialInterior_mem_selected hQ hi)).1
  exact congrArg (fun z : ℝ => z ^ 2) (h P hP x hx y hy)

end ReyZygmund.Geometry
