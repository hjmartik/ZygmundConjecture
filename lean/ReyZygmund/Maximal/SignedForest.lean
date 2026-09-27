import ReyZygmund.Maximal.SignedFinite
import ReyZygmund.Maximal.Signed
import ReyZygmund.Geometry.ProductContainment
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! # Signed averages localized to disjoint top rectangles

Assign each averaging rectangle to the top rectangle containing it. Equality of
inputs there preserves its signed average. Rectangles assigned to other top
rectangles contribute zero at the point in question.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

theorem finiteSignedGridMaximal_zero_off_forest
    (T A : Finset (∀ i, Box (Fin (d i))))
    (hcover : ∀ Q ∈ A, ∃ R ∈ T, ∀ i, Q i ≤ R i)
    (f : ProductPoint d → ℝ) (x : ProductPoint d)
    (hx : x ∉ ⋃ R ∈ T, productBox R) : finiteSignedGridMaximal A f x = 0 := by
  apply le_antisymm _ zero_le
  apply Finset.sup_le
  intro Q hQ
  obtain ⟨R, hR, hQR⟩ := hcover Q hQ
  have hxQ : x ∉ productBox Q := fun h =>
    hx (Set.mem_iUnion₂.mpr ⟨R, hR, (productBox_subset_iff Q R).mpr hQR h⟩)
  simp only [Set.indicator_of_notMem hxQ, ENNReal.ofReal_zero, le_refl]

theorem finiteSignedGridMaximal_le_on_root
    (T A : Finset (∀ i, Box (Fin (d i))))
    (hdis : Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (productBox R) (productBox S)))
    (hcover : ∀ Q ∈ A, ∃ R ∈ T, ∀ i, Q i ≤ R i)
    (R : ∀ i, Box (Fin (d i))) (hR : R ∈ T) (N : Fin m → ℕ)
    (hcut : A.filter (fun Q => ∀ i, Q i ≤ R i) ⊆ productDescendants R N)
    (f : ProductPoint d → ℝ) (S : boundedMeasurableFunctions d)
    (heq : ∀ x ∈ productBox R, f x = S.1 x)
    (x : ProductPoint d) (hx : x ∈ productBox R) :
    finiteSignedGridMaximal A f x ≤ ENNReal.ofReal (finiteSignedProductMaximal R N S x) := by
  apply Finset.sup_le
  intro Q hQ
  by_cases hQR : ∀ i, Q i ≤ R i
  · have hQI : Q ∈ productDescendants R N := hcut (Finset.mem_filter.mpr ⟨hQ, hQR⟩)
    have hav : (∫ y in productBox Q, f y) = ∫ y in productBox Q, S.1 y :=
      setIntegral_congr_fun (measurableSet_productBox Q)
        (fun y hy => heq y ((productBox_subset_iff Q R).mpr hQR hy))
    apply ENNReal.ofReal_le_ofReal
    have hle := Finset.le_sup' (fun P => |(productAverageMap Finset.univ P S).1 x|) hQI
    change _ ≤ finiteSignedProductMaximal R N S x at hle
    rw [productAverageMap_univ_eq_integral] at hle
    by_cases hxQ : x ∈ productBox Q
    · simpa only [Set.indicator_of_mem hxQ, hav] using hle
    · simp only [Set.indicator_of_notMem hxQ]
      exact finiteSignedProductMaximal_nonneg R N S x
  · obtain ⟨P, hP, hQP⟩ := hcover Q hQ
    have hPR : P ≠ R := by rintro rfl; exact hQR hQP
    have hxQ : x ∉ productBox Q := fun h =>
      Set.disjoint_left.mp (hdis hP hR hPR)
        ((productBox_subset_iff Q P).mpr hQP h) hx
    simp only [Set.indicator_of_notMem hxQ, ENNReal.ofReal_zero, zero_le]

theorem lintegral_finiteSignedGridMaximal_forest_le
    (T A : Finset (∀ i, Box (Fin (d i))))
    (hdis : Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (productBox R) (productBox S)))
    (hcover : ∀ Q ∈ A, ∃ R ∈ T, ∀ i, Q i ≤ R i)
    (N : Fin m → ℕ)
    (hcut : ∀ R ∈ T, A.filter (fun Q => ∀ i, Q i ≤ R i) ⊆ productDescendants R N)
    (f : ProductPoint d → ℝ) (S : (∀ i, Box (Fin (d i))) → boundedMeasurableFunctions d)
    (heq : ∀ R ∈ T, ∀ x ∈ productBox R, f x = (S R).1 x)
    (p : ℝ) (hp : 0 < p) :
    (∫⁻ x, (finiteSignedGridMaximal A f x) ^ p) ≤
      ∑ R ∈ T, ∫⁻ x in productBox R,
        (ENNReal.ofReal (finiteSignedProductMaximal R N (S R) x)) ^ p := by
  let U : Set (ProductPoint d) := ⋃ R ∈ T, productBox R
  have hmU : MeasurableSet U := MeasurableSet.biUnion T.countable_toSet
    (fun R _ => measurableSet_productBox R)
  have he : U.indicator (fun x => (finiteSignedGridMaximal A f x) ^ p) =
      fun x => (finiteSignedGridMaximal A f x) ^ p := by
    funext x
    by_cases hx : x ∈ U
    · exact Set.indicator_of_mem hx _
    · rw [Set.indicator_of_notMem hx,
        finiteSignedGridMaximal_zero_off_forest T A hcover f x hx,
        ENNReal.zero_rpow_of_pos hp]
  calc
    _ = ∫⁻ x in U, (finiteSignedGridMaximal A f x) ^ p := by
      rw [← lintegral_indicator hmU, he]
    _ = ∑ R ∈ T, ∫⁻ x in productBox R, (finiteSignedGridMaximal A f x) ^ p :=
      lintegral_biUnion_finset hdis (fun R _ => measurableSet_productBox R) _
    _ ≤ _ := Finset.sum_le_sum (fun R hR => lintegral_mono_ae (by
      filter_upwards [ae_restrict_mem (measurableSet_productBox R)] with x hx
      exact ENNReal.rpow_le_rpow (finiteSignedGridMaximal_le_on_root T A hdis hcover R hR N
        (hcut R hR) f (S R) (heq R hR) x hx) hp.le))

end ReyZygmund
