import ReyZygmund.Geometry.RawDifferenceProperties
import ReyZygmund.Geometry.ProductClosure

/-! # Full differences as finite step functions

Every child or parent rectangle in the expansion lies inside the indexing
rectangle. At scales fine enough to include those children, its indicator is
constant on each smallest cube. These properties do not require a grid or
integrability of the original input.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

open Projection

variable {m : ℕ} {d : Fin m → ℕ}

theorem productLeafConstant_descendant_indicator
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (P : ∀ i, Box (Fin (d i))) (hP : P ∈ productDescendants I N) (c : ℝ) :
    ProductLeafConstant I N ((productBox P).indicator (fun _ => c)) := by
  intro L hL x hx y hy
  have hmem : ∀ z ∈ productBox L, ∀ t ∈ productBox L,
      z ∈ productBox P → t ∈ productBox P := by
    intro z hz t ht hzp
    apply (mem_productBox P t).mpr
    intro i
    obtain ⟨n, hn, hPn⟩ := mem_descendants.mp (Fintype.mem_piFinset.mp hP i)
    rcases level_le_or_disjoint hn (Fintype.mem_piFinset.mp hL i) hPn with hLP | hdis
    · exact hLP ((mem_productBox L t).mp ht i)
    · exact (Set.disjoint_left.mp hdis ((mem_productBox L z).mp hz i)
        ((mem_productBox P z).mp hzp i)).elim
  by_cases hxp : x ∈ productBox P
  · rw [Set.indicator_of_mem hxp, Set.indicator_of_mem (hmem x hx y hy hxp)]
  · rw [Set.indicator_of_notMem hxp,
      Set.indicator_of_notMem (fun hyp => hxp (hmem y hy x hx hyp))]

theorem differenceRectangles_le (A : Finset (Fin m))
    (Q R : ∀ i, Box (Fin (d i))) (hR : R ∈ differenceRectangles A Q) :
    ∀ i, R i ≤ Q i := by
  intro i
  have hi := Fintype.mem_piFinset.mp hR i
  by_cases hia : i ∈ A
  · have hchild : R i ∈ Prepartition.splitCenter (Q i) := by
      simpa only [ite_eq_left hia, Prepartition.mem_boxes] using hi
    exact (Prepartition.splitCenter (Q i)).le_of_mem hchild
  · have heq : R i = Q i := by simpa only [ite_eq_right hia, Finset.mem_singleton] using hi
    exact heq.le

theorem differenceRectangles_mem_descendants
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A : Finset (Fin m)) (Q R : ∀ i, Box (Fin (d i)))
    (hQ : Q ∈ productInterior I N) (hR : R ∈ differenceRectangles A Q) :
    R ∈ productDescendants I N := by
  apply Fintype.mem_piFinset.mpr
  intro i
  have hi := Fintype.mem_piFinset.mp hR i
  have hQi := Fintype.mem_piFinset.mp hQ i
  by_cases hia : i ∈ A
  · apply ProductClosure.child_mem_descendants hQi
    simpa only [ite_eq_left hia, Prepartition.mem_boxes] using hi
  · have heq : R i = Q i := by simpa only [ite_eq_right hia, Finset.mem_singleton] using hi
    rw [heq]
    exact interior_subset_descendants (I i) (N i) hQi

theorem productLeafConstant_rawProductDifference
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (Q : ∀ i, Box (Fin (d i))) (hQ : Q ∈ productInterior I N)
    (g : ProductPoint d → ℝ) : ProductLeafConstant I N (rawProductDifference Q g) := by
  intro L hL x hx y hy
  apply Finset.sum_congr rfl
  intro A _
  congr 1
  apply Finset.sum_congr rfl
  intro R hR
  exact productLeafConstant_descendant_indicator I N R
    (differenceRectangles_mem_descendants I N A Q R hQ hR) _ L hL x hx y hy

theorem rawProductDifference_eq_zero_of_notMem
    (Q : ∀ i, Box (Fin (d i))) (g : ProductPoint d → ℝ)
    (x : ProductPoint d) (hx : x ∉ productBox Q) : rawProductDifference Q g x = 0 := by
  apply Finset.sum_eq_zero
  intro A _
  have hz : (∑ R ∈ differenceRectangles A Q,
      (productBox R).indicator
        (fun _ => (∫ y in productBox R, g y) / volume.real (productBox R)) x) = 0 := by
    apply Finset.sum_eq_zero
    intro R hR
    apply Set.indicator_of_notMem
    intro hxr
    apply hx
    exact (mem_productBox Q x).mpr (fun i =>
      differenceRectangles_le A Q R hR i ((mem_productBox R x).mp hxr i))
  exact mul_eq_zero_of_right _ hz

end ReyZygmund.Geometry
