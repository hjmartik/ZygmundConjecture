import ReyZygmund.Geometry.ProductMaps
import ReyZygmund.Geometry.ProductIntegrability
import ReyZygmund.Geometry.ProductJensen
import ReyZygmund.Projection.AveragingRectangles
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Averaging on the smallest product cubes

Sum the supported, normalized Lebesgue averages over the smallest product cubes.
This finite step function gives the input reduction used in the paper.


-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Geometry

open Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- Averaging on the finite smallest product cubes, zero off their union. -/
noncomputable def leafAverage
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (f : ProductPoint d → ℝ) :
    ProductPoint d → ℝ :=
  fun x => ∑ Q ∈ productLeaves I N,
    (productBox Q).indicator
      (fun _ => (∫ y in productBox Q, f y) / volume.real (productBox Q)) x

theorem leafAverage_of_mem
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (f : ProductPoint d → ℝ)
    (Q : ∀ i, Box (Fin (d i))) (hQ : Q ∈ productLeaves I N)
    (x : ProductPoint d) (hx : x ∈ productBox Q) :
    leafAverage I N f x = (∫ y in productBox Q, f y) / volume.real (productBox Q) := by
  rw [leafAverage, Finset.sum_eq_single Q]
  · exact Set.indicator_of_mem hx _
  · intro R hR hRQ
    exact Set.indicator_of_notMem
      (fun hxR => hRQ (productLeaves_unique hR hQ hxR hx)) _
  · simp only [hQ, not_true_eq_false, false_implies]

theorem productLeafConstant_leafAverage
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (f : ProductPoint d → ℝ) :
    ProductLeafConstant I N (leafAverage I N f) := by
  intro Q hQ x hx y hy
  rw [leafAverage_of_mem I N f Q hQ x hx, leafAverage_of_mem I N f Q hQ y hy]

theorem leafAverage_eq_zero_of_notMem
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (f : ProductPoint d → ℝ)
    (x : ProductPoint d) (hx : x ∉ productBox I) : leafAverage I N f x = 0 := by
  apply Finset.sum_eq_zero
  intro Q hQ
  exact Set.indicator_of_notMem (fun hxQ => hx (productLeaves_subset hQ hxQ)) _

theorem leafAverage_nonneg
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (f : ProductPoint d → ℝ)
    (hf : ∀ x ∈ productBox I, 0 ≤ f x) (x : ProductPoint d) :
    0 ≤ leafAverage I N f x := by
  apply Finset.sum_nonneg
  intro Q hQ
  apply Set.indicator_nonneg _ x
  intro _ _
  apply div_nonneg _ measureReal_nonneg
  exact integral_nonneg_of_ae (ae_restrict_of_forall_mem (measurableSet_productBox Q)
    (fun y hy => hf y (productLeaves_subset hQ hy)))

private theorem leaf_below_descendant_of_mem
    {I : ∀ i, Box (Fin (d i))} {N : Fin m → ℕ}
    {Q R : ∀ i, Box (Fin (d i))}
    (hQ : Q ∈ productLeaves I N) (hR : R ∈ productDescendants I N)
    {x : ProductPoint d} (hxQ : x ∈ productBox Q) (hxR : x ∈ productBox R) :
    ∀ i, Q i ≤ R i := by
  intro i
  obtain ⟨n, hn, hRn⟩ := mem_descendants.mp (mem_productDescendants.mp hR i)
  rcases level_le_or_disjoint hn (Fintype.mem_piFinset.mp hQ i) hRn with h | h
  · exact h
  · exact False.elim (Set.disjoint_left.mp h
      ((mem_productBox Q x).mp hxQ i) ((mem_productBox R x).mp hxR i))

private theorem productBox_mono
    {Q R : ∀ i, Box (Fin (d i))} (h : ∀ i, Q i ≤ R i) :
    productBox Q ⊆ productBox R := by
  intro x hx
  exact (mem_productBox R x).mpr (fun i => h i ((mem_productBox Q x).mp hx i))

private theorem descendant_eq_union_leaves
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (R : ∀ i, Box (Fin (d i))) (hR : R ∈ productDescendants I N) :
    (⋃ Q ∈ (productLeaves I N).filter (fun Q => ∀ i, Q i ≤ R i), productBox Q) =
      productBox R := by
  ext x
  constructor
  · intro hx
    obtain ⟨Q, hQ, hxQ⟩ := Set.mem_iUnion₂.mp hx
    exact productBox_mono (Finset.mem_filter.mp hQ).2 hxQ
  · intro hx
    obtain ⟨Q, hQ, hxQ⟩ := productLeaves_cover I N x
      (productBox_subset_root_of_mem_productDescendants hR hx)
    exact Set.mem_iUnion₂.mpr ⟨Q, Finset.mem_filter.mpr
      ⟨hQ, leaf_below_descendant_of_mem hQ hR hxQ hx⟩, hxQ⟩

private theorem productLeaves_pairwise_disjoint
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) :
    Set.Pairwise (↑(productLeaves I N))
      (fun (Q R : ∀ i, Box (Fin (d i))) => Disjoint (productBox Q) (productBox R)) := by
  intro Q hQ R hR hne
  apply Set.disjoint_left.mpr
  intro x hxQ hxR
  exact hne (productLeaves_unique hQ hR hxQ hxR)

/-- The integral over a retained rectangle is the sum of integrals over its smallest
product cubes. Values outside the top rectangle are unrestricted. -/
theorem integral_descendant_eq_sum_leaves
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (R : ∀ i, Box (Fin (d i))) (hR : R ∈ productDescendants I N)
    (f : ProductPoint d → ℝ) (hf : IntegrableOn f (productBox I) volume) :
    (∫ x in productBox R, f x) =
      ∑ Q ∈ (productLeaves I N).filter (fun Q => ∀ i, Q i ≤ R i),
        ∫ x in productBox Q, f x := by
  rw [← descendant_eq_union_leaves I N R hR]
  apply integral_biUnion_finset
  · exact fun Q _ => measurableSet_productBox Q
  · intro Q hQ S hS hne
    exact productLeaves_pairwise_disjoint I N
      (Finset.mem_filter.mp hQ).1 (Finset.mem_filter.mp hS).1 hne
  · exact fun Q hQ => hf.mono_set (productLeaves_subset (Finset.mem_filter.mp hQ).1)

/-- Averaging preserves the integral on each smallest cube. -/
theorem integral_leafAverage_leaf
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (f : ProductPoint d → ℝ)
    (Q : ∀ i, Box (Fin (d i))) (hQ : Q ∈ productLeaves I N) :
    (∫ x in productBox Q, leafAverage I N f x) = ∫ x in productBox Q, f x := by
  calc
    _ = ∫ _x in productBox Q,
        (∫ y in productBox Q, f y) / volume.real (productBox Q) :=
      setIntegral_congr_fun (measurableSet_productBox Q)
        (fun x hx => leafAverage_of_mem I N f Q hQ x hx)
    _ = _ := by
      rw [setIntegral_const, smul_eq_mul, mul_div_cancel₀ _ (productBox_volume_pos Q).ne']

/-- Averaging on the smallest cubes preserves each retained rectangle average. The
input need only be integrable on the top rectangle. -/
theorem integral_leafAverage_descendant
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (R : ∀ i, Box (Fin (d i))) (hR : R ∈ productDescendants I N)
    (f : ProductPoint d → ℝ) (hf : IntegrableOn f (productBox I) volume) :
    (∫ x in productBox R, leafAverage I N f x) = ∫ x in productBox R, f x := by
  rw [integral_descendant_eq_sum_leaves I N R hR _
    (integrableOn_productLeafConstant I N _ (productLeafConstant_leafAverage I N f)),
    integral_descendant_eq_sum_leaves I N R hR f hf]
  apply Finset.sum_congr rfl
  intro Q hQ
  exact integral_leafAverage_leaf I N f Q (Finset.mem_filter.mp hQ).1

/-- Averaging on the smallest cubes contracts the integral of each absolute p-th
power, with coefficient one. Values outside the top rectangle are unrestricted. -/
theorem integral_abs_rpow_leafAverage_le
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (f : ProductPoint d → ℝ)
    (p : ℝ) (hp : 1 ≤ p) (hf : IntegrableOn f (productBox I) volume)
    (hpow : IntegrableOn (fun x => Real.rpow |f x| p) (productBox I) volume) :
    (∫ x in productBox I, Real.rpow |leafAverage I N f x| p) ≤
      ∫ x in productBox I, Real.rpow |f x| p := by
  have hleaf : ProductLeafConstant I N
      (fun x => Real.rpow |leafAverage I N f x| p) := by
    intro Q hQ x hx y hy
    dsimp only
    rw [productLeafConstant_leafAverage I N f Q hQ x hx y hy]
  rw [integral_descendant_eq_sum_leaves I N I (root_mem_productDescendants I N) _
    (integrableOn_productLeafConstant I N _ hleaf),
    integral_descendant_eq_sum_leaves I N I (root_mem_productDescendants I N) _ hpow]
  apply Finset.sum_le_sum
  intro Q hQ
  have hQleaf := (Finset.mem_filter.mp hQ).1
  calc
    _ = volume.real (productBox Q) *
        Real.rpow |(∫ y in productBox Q, f y) / volume.real (productBox Q)| p := by
      rw [← smul_eq_mul, ← setIntegral_const]
      apply setIntegral_congr_fun (measurableSet_productBox Q)
      intro x hx
      dsimp only
      rw [leafAverage_of_mem I N f Q hQleaf x hx]
    _ ≤ volume.real (productBox Q) *
        ((∫ x in productBox Q, Real.rpow |f x| p) / volume.real (productBox Q)) :=
      mul_le_mul_of_nonneg_left
        (productBox_average_abs_rpow Q f p hp
          (hf.mono_set (productLeaves_subset hQleaf))
          (hpow.mono_set (productLeaves_subset hQleaf)))
        (productBox_volume_pos Q).le
    _ = _ := mul_div_cancel₀ _ (productBox_volume_pos Q).ne'

end ReyZygmund.Geometry
