import ReyZygmund.Geometry.GridProductAlgebra
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Finite expansions on the full product grid

Orthogonality makes differences outside the finite expansion vanish, reducing the
square series to a finite sum. Average cancellation uses the same bounded
measurable representative. The grid itself need not have a common top rectangle or
a smallest scale.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem grid_rawProductDifference_same_of_mem
    (D : ∀ i, DyadicGrid (d i)) (hd : ∀ i, 0 < d i)
    (L Q : ∀ i, Box (Fin (d i)))
    (hL : L ∈ gridRectangles D) (hQ : Q ∈ gridRectangles D)
    (F : boundedMeasurableFunctions d) :
    rawProductDifference L (rawProductDifference Q F.1) =
      if L = Q then rawProductDifference Q F.1 else 0 := by
  choose a ha using hL
  choose b hb using hQ
  exact grid_rawProductDifference_same D a b hd L Q ha hb F

/-- A full difference selects its matching term from the finite
expansion, including the matching and empty-family branches. -/
theorem grid_rawProductDifference_sum
    (D : ∀ i, DyadicGrid (d i)) (hd : ∀ i, 0 < d i)
    (H : Finset (∀ i, Box (Fin (d i))))
    (hH : (↑H : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D)
    (F : boundedMeasurableFunctions d) (L : ∀ i, Box (Fin (d i)))
    (hL : L ∈ gridRectangles D) :
    rawProductDifference L (fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x) =
      if L ∈ H then rawProductDifference L F.1 else 0 := by
  let S : boundedMeasurableFunctions d := ∑ Q ∈ H, productDifferenceMap Finset.univ Q F
  have hS : S.1 = fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x := by
    funext x
    simp [S, Finset.sum_apply, rawProductDifference_eq_productDifferenceMap]
  have hlin : (productDifferenceMap Finset.univ L S).1 =
      fun x => ∑ Q ∈ H, rawProductDifference L (rawProductDifference Q F.1) x := by
    funext x
    simp [S, Finset.sum_apply, rawProductDifference_eq_productDifferenceMap]
  rw [← hS, rawProductDifference_eq_productDifferenceMap L S, hlin]
  funext x
  have hc : (∑ Q ∈ H, rawProductDifference L (rawProductDifference Q F.1) x) =
      ∑ Q ∈ H, if L = Q then rawProductDifference Q F.1 x else 0 := by
    apply Finset.sum_congr rfl
    intro Q hQ
    have ht := congrFun (grid_rawProductDifference_same_of_mem D hd L Q hL (hH hQ) F) x
    by_cases heq : L = Q <;> simpa only [heq, ite_true, ite_false, Pi.zero_apply] using ht
  rw [hc]
  by_cases hmem : L ∈ H <;> simp [hmem]

/-- The finite expansion itself forces all other grid differences to
vanish; finite support is a conclusion, not an input field. -/
theorem grid_rawProductDifference_eq_zero_of_not_mem
    (D : ∀ i, DyadicGrid (d i)) (hd : ∀ i, 0 < d i)
    (H : Finset (∀ i, Box (Fin (d i))))
    (hH : (↑H : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D)
    (F : boundedMeasurableFunctions d)
    (hex : F.1 = fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x)
    (L : ∀ i, Box (Fin (d i))) (hL : L ∈ gridRectangles D) (hnot : L ∉ H) :
    rawProductDifference L F.1 = 0 := by
  calc
    rawProductDifference L F.1 =
        rawProductDifference L (fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x) :=
      congrArg (rawProductDifference L) hex
    _ = 0 := by rw [grid_rawProductDifference_sum D hd H hH F L hL, ite_eq_right hnot]

/-- The full-grid extended square series reduces to the proved finite
support. The identity is pointwise and retains the real square-root exponent. -/
theorem fullGridSquare_eq_finite_expansion
    (D : ∀ i, DyadicGrid (d i)) (hd : ∀ i, 0 < d i)
    (H : Finset (∀ i, Box (Fin (d i))))
    (hH : (↑H : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D)
    (F : boundedMeasurableFunctions d)
    (hex : F.1 = fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x)
    (x : ProductPoint d) :
    fullGridSquare D F.1 x =
      (∑ Q ∈ H, (ENNReal.ofReal |rawProductDifference Q F.1 x|) ^ 2) ^ (1 / 2 : ℝ) := by
  let f : (∀ i, Box (Fin (d i))) → ℝ≥0∞ :=
    fun Q => (ENNReal.ofReal |rawProductDifference Q F.1 x|) ^ 2
  have hs : (∑' L : gridRectangles D, f L.1) = ∑ Q ∈ H, f Q := by
    rw [tsum_subtype]
    calc
      (∑' L, (gridRectangles D).indicator f L) =
          ∑ L ∈ H, (gridRectangles D).indicator f L := by
        apply tsum_eq_sum
        intro L hnot
        by_cases hL : L ∈ gridRectangles D
        · rw [Set.indicator_of_mem hL]
          have hz := grid_rawProductDifference_eq_zero_of_not_mem D hd H hH F hex L hL hnot
          simp [f, hz]
        · exact Set.indicator_of_notMem hL f
      _ = ∑ Q ∈ H, f Q := by
        apply Finset.sum_congr rfl
        intro Q hQ
        exact Set.indicator_of_mem (hH hQ) f
  simpa only [fullGridSquare, f] using
    congrArg (fun z : ℝ≥0∞ => z ^ (1 / 2 : ℝ)) hs

/-- An average of the represented function vanishes when every
expansion rectangle has a coordinate failing strict containment. -/
theorem grid_productAverage_finite_expansion_eq_zero
    (D : ∀ i, DyadicGrid (d i)) (hd : ∀ i, 0 < d i)
    (H : Finset (∀ i, Box (Fin (d i))))
    (hH : (↑H : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D)
    (F : boundedMeasurableFunctions d)
    (hex : F.1 = fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x)
    (R : ∀ i, Box (Fin (d i))) (hR : R ∈ gridRectangles D)
    (hbad : ∀ Q ∈ H, ∃ i, ¬ R i < Q i) :
    productAverageMap Finset.univ R F = 0 := by
  have hF : F = ∑ Q ∈ H, productDifferenceMap Finset.univ Q F := by
    apply Subtype.ext
    funext x
    simpa [rawProductDifference_eq_productDifferenceMap, Finset.sum_apply] using congrFun hex x
  choose a ha using hR
  rw [hF, map_sum]
  apply Finset.sum_eq_zero
  intro Q hQ
  choose b hb using hH hQ
  obtain ⟨i, hnot⟩ := hbad Q hQ
  have hz := grid_productAverageMap_mul_full_difference_eq_zero D a b Finset.univ R Q
    (fun j _ => ha j) hb ⟨i, Finset.mem_univ i, hd i, hnot⟩
  change (productAverageMap Finset.univ R * productDifferenceMap Finset.univ Q) F = 0
  rw [hz, LinearMap.zero_apply]

/-- Normalized signed rectangle means inherit the map cancellation. -/
theorem grid_mean_finite_expansion_eq_zero
    (D : ∀ i, DyadicGrid (d i)) (hd : ∀ i, 0 < d i)
    (H : Finset (∀ i, Box (Fin (d i))))
    (hH : (↑H : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D)
    (F : boundedMeasurableFunctions d)
    (hex : F.1 = fun x => ∑ Q ∈ H, rawProductDifference Q F.1 x)
    (R : ∀ i, Box (Fin (d i))) (hR : R ∈ gridRectangles D)
    (hbad : ∀ Q ∈ H, ∃ i, ¬ R i < Q i) :
    (∫ x in productBox R, F.1 x) / volume.real (productBox R) = 0 := by
  let x : ProductPoint d := fun i => (R i).upper
  have hx : x ∈ productBox R := (mem_productBox R x).mpr (fun i => (R i).upper_mem)
  have hz := congrArg (fun G : boundedMeasurableFunctions d => G.1 x)
    (grid_productAverage_finite_expansion_eq_zero D hd H hH F hex R hR hbad)
  simpa only [productAverageMap_univ_eq_integral, Set.indicator_of_mem hx,
    ZeroMemClass.coe_zero, Pi.zero_apply] using hz

end ReyZygmund.Geometry
