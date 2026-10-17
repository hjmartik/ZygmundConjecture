import ReyZygmund.Geometry.ProductFiniteSetting
import ReyZygmund.Geometry.PartialOperatorMaps
import ReyZygmund.Geometry.FiniteSquare
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! # Partial square functions on a finite product grid

The public partial tuples correspond to finite difference indices, with each
unselected factor fixed at the top cube. Thus their nonnegative sums are the
finite sums of squares, and the real square roots give the same functions.
-/

open BoxIntegral
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.Geometry

open MathlibOnly (CubeGrid Rectangle)

variable {m : ℕ} {d : Fin m → ℕ}

/-- The extended-valued partial square function agrees with the finite
real-valued square function. -/
theorem partialSquareFunction_eq_ofReal
    (D : ∀ i, CubeGrid (d i)) {I : Rectangle d} {l : Fin m → ℤ} {k : ℤ}
    (hI : ∀ i, I i ∈ (D i).cubes (l i)) (hcut : ∀ i, -k ≤ l i)
    (A : Finset (Fin m)) (hd : ∀ i ∈ A, 0 < d i)
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) :
    MathlibOnly.partialSquareFunction D I k A F.1 x =
      ENNReal.ofReal (finiteSquareFunction I (fun i => (l i + k).toNat) A F x) := by
  rw [MathlibOnly.partialSquareFunction,
    tsum_partialInterior_eq D hI hcut A hd
      (fun K => ENNReal.ofReal |MathlibOnly.partialDifference A K F.1 x| ^ 2)]
  simp_rw [partialDifference_eq_productDifferenceMap A _ F,
    ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
    finiteSquareFunction, Real.sqrt_eq_rpow,
    ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- The combined square function agrees with the finite expression `W F`: the
square root of the sum of squared partial square functions. -/
theorem combinedSquareFunction_eq_ofReal
    (D : ∀ i, CubeGrid (d i)) {I : Rectangle d} {l : Fin m → ℤ} {k : ℤ}
    (hI : ∀ i, I i ∈ (D i).cubes (l i)) (hcut : ∀ i, -k ≤ l i)
    (hd : ∀ i, 0 < d i) (F : boundedMeasurableFunctions d) (x : ProductPoint d) :
    MathlibOnly.combinedSquareFunction D I k F.1 x =
      ENNReal.ofReal (finiteComplementSquareFunction I (fun i => (l i + k).toNat) F x) := by
  rw [MathlibOnly.combinedSquareFunction]
  simp_rw [partialSquareFunction_eq_ofReal D hI hcut _ (fun i _ => hd i) F x]
  have hsq (j : Fin m) :
      ENNReal.ofReal (finiteSquareFunction I (fun i => (l i + k).toNat)
        (Finset.univ.erase j) F x) ^ 2 =
      ENNReal.ofReal (finiteSquareFunction I (fun i => (l i + k).toNat)
        (Finset.univ.erase j) F x ^ 2) :=
    (ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2).symm
  simp_rw [hsq]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
    finiteComplementSquareFunction_eq_partial, Real.sqrt_eq_rpow,
    ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]

end ReyZygmund.Geometry
