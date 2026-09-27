import ReyZygmund.Geometry.RawDifferenceSteps
import ReyZygmund.Geometry.RawDifferenceBridge
import ReyZygmund.Geometry.ProductOrthogonality
import ReyZygmund.Geometry.FiniteSquare

/-! # A finite difference expansion inside a top rectangle

Each full difference is a step function supported in its indexing rectangle. A
finite sum of interior differences is therefore supported in the top rectangle and
constant on sufficiently small cubes, even when the original bounded measurable
input is not. Orthogonality gives the expansion and finite square identities.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

open Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- A finite sum of interior differences is a finite step function supported on the
top rectangle, even without those properties for the input. -/
theorem finite_difference_sum_productStep
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (H : Finset (∀ i, Box (Fin (d i)))) (hH : H ⊆ productInterior I N)
    (F : boundedMeasurableFunctions d) :
    let S := ∑ Q ∈ H, productDifferenceMap Finset.univ Q F
    ProductLeafConstant I N S.1 ∧ ∀ x, x ∉ productBox I → S.1 x = 0 := by
  dsimp only
  have hsum : (∑ Q ∈ H, productDifferenceMap Finset.univ Q F).1 =
      ∑ Q ∈ H, (productDifferenceMap Finset.univ Q F).1 := by
    funext x
    simp [Finset.sum_apply]
  rw [hsum]
  constructor
  · apply productLeafConstant_finsetSum
    intro Q hQ
    rw [← rawProductDifference_eq_productDifferenceMap Q F]
    exact productLeafConstant_rawProductDifference I N Q (hH hQ) F.1
  · intro x hx
    simp only [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro Q hQ
    rw [← rawProductDifference_eq_productDifferenceMap Q F]
    apply rawProductDifference_eq_zero_of_notMem Q F.1 x
    intro hxQ
    apply hx
    apply (mem_productBox I x).mpr
    intro i
    exact le_of_mem_descendants
      (interior_subset_descendants (I i) (N i) ((mem_productInterior.mp (hH hQ)) i))
      ((mem_productBox Q x).mp hxQ i)

private theorem difference_sum_coefficient
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (H : Finset (∀ i, Box (Fin (d i)))) (hH : H ⊆ productInterior I N)
    (F : boundedMeasurableFunctions d) (L : ∀ i, Box (Fin (d i)))
    (hL : L ∈ productInterior I N) :
    productDifferenceMap Finset.univ L
      (∑ Q ∈ H, productDifferenceMap Finset.univ Q F) =
        if L ∈ H then productDifferenceMap Finset.univ L F else 0 := by
  rw [map_sum]
  have hterm : ∀ Q ∈ H,
      productDifferenceMap Finset.univ L (productDifferenceMap Finset.univ Q F) =
        if L = Q then productDifferenceMap Finset.univ Q F else 0 := by
    intro Q hQ
    have hop : productDifferenceMap Finset.univ L * productDifferenceMap Finset.univ Q =
        if L = Q then productDifferenceMap Finset.univ Q else 0 := by
      rw [productDifferenceMap_mul_full I N hd Finset.univ L Q
        (fun i _ => interior_subset_descendants (I i) (N i)
          ((mem_productInterior.mp hL) i))
        (fun i => interior_subset_descendants (I i) (N i)
          ((mem_productInterior.mp (hH hQ)) i))]
      congr 1
      exact propext ⟨fun h => funext (fun i => h i (Finset.mem_univ i)),
        fun h i _ => congrFun h i⟩
    have ht := congrArg (fun T : Module.End ℝ (boundedMeasurableFunctions d) => T F) hop
    by_cases heq : L = Q <;>
      simpa only [Module.End.mul_apply, heq, ite_true, ite_false, LinearMap.zero_apply] using ht
  calc
    _ = ∑ Q ∈ H, if L = Q then productDifferenceMap Finset.univ Q F else 0 :=
      Finset.sum_congr rfl hterm
    _ = _ := by simp

/-- The localized sum is its full-tree difference expansion, as an
equality in the bounded measurable function space. -/
theorem finite_difference_sum_reexpansion
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (H : Finset (∀ i, Box (Fin (d i)))) (hH : H ⊆ productInterior I N)
    (F : boundedMeasurableFunctions d) :
    let S := ∑ Q ∈ H, productDifferenceMap Finset.univ Q F
    S = ∑ L ∈ productInterior I N, productDifferenceMap Finset.univ L S := by
  let S : boundedMeasurableFunctions d := ∑ Q ∈ H, productDifferenceMap Finset.univ Q F
  change S = ∑ L ∈ productInterior I N, productDifferenceMap Finset.univ L S
  have hc : ∀ L ∈ productInterior I N,
      productDifferenceMap Finset.univ L S =
        if L ∈ H then productDifferenceMap Finset.univ L F else 0 :=
    fun L hL => difference_sum_coefficient I N hd H hH F L hL
  calc
    S = ∑ L ∈ H, productDifferenceMap Finset.univ L S := by
      change (∑ L ∈ H, productDifferenceMap Finset.univ L F) = _
      apply Finset.sum_congr rfl
      intro L hL
      rw [hc L (hH hL), ite_eq_left hL]
    _ = ∑ L ∈ productInterior I N, productDifferenceMap Finset.univ L S := by
      apply Finset.sum_subset hH
      intro L hL hnot
      rw [hc L hL, ite_eq_right hnot]

/-- The localized square contains exactly the original selected coefficients;
the omitted interior terms vanish by orthogonality. -/
theorem finite_difference_sum_square_eq
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (H : Finset (∀ i, Box (Fin (d i)))) (hH : H ⊆ productInterior I N)
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) :
    let S := ∑ Q ∈ H, productDifferenceMap Finset.univ Q F
    finiteSquareFunction I N Finset.univ S x =
      Real.sqrt (∑ Q ∈ H, ((productDifferenceMap Finset.univ Q F).1 x) ^ 2) := by
  let S : boundedMeasurableFunctions d := ∑ Q ∈ H, productDifferenceMap Finset.univ Q F
  change finiteSquareFunction I N Finset.univ S x = _
  have hc : ∀ L ∈ productInterior I N,
      productDifferenceMap Finset.univ L S =
        if L ∈ H then productDifferenceMap Finset.univ L F else 0 :=
    fun L hL => difference_sum_coefficient I N hd H hH F L hL
  have hindices : partialInterior I N Finset.univ = productInterior I N := by
    simp only [partialInterior, productInterior, Finset.mem_univ, ite_true]
  rw [finiteSquareFunction, hindices]
  apply congrArg Real.sqrt
  calc
    (∑ L ∈ productInterior I N, ((productDifferenceMap Finset.univ L S).1 x) ^ 2) =
        ∑ L ∈ H, ((productDifferenceMap Finset.univ L S).1 x) ^ 2 := by
      symm
      apply Finset.sum_subset hH
      intro L hL hnot
      have hz : productDifferenceMap Finset.univ L S = 0 := by
        rw [hc L hL, ite_eq_right hnot]
      simp [hz]
    _ = ∑ L ∈ H, ((productDifferenceMap Finset.univ L F).1 x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro L hL
      rw [hc L (hH hL), ite_eq_left hL]

end ReyZygmund.Geometry
