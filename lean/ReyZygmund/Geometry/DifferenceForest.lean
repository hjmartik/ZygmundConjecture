import ReyZygmund.Geometry.FiniteExpansionSquare
import ReyZygmund.Geometry.ProductContainment

/-! # Localization of a finite difference expansion

The top rectangles are pairwise disjoint. On each one, differences assigned to the
others vanish. Summing the local estimates therefore counts the function and its
square once.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem raw_difference_zero_on_other_root
    (T H : Finset (∀ i, Box (Fin (d i))))
    (hdis : Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (productBox R) (productBox S)))
    (hcover : ∀ Q ∈ H, ∃ R ∈ T, ∀ i, Q i ≤ R i)
    (f : ProductPoint d → ℝ) (R : ∀ i, Box (Fin (d i))) (hR : R ∈ T)
    (Q : ∀ i, Box (Fin (d i))) (hQ : Q ∈ H) (hnot : ¬ ∀ i, Q i ≤ R i)
    (x : ProductPoint d) (hx : x ∈ productBox R) : rawProductDifference Q f x = 0 := by
  obtain ⟨S, hS, hQS⟩ := hcover Q hQ
  have hSR : S ≠ R := by rintro rfl; exact hnot hQS
  apply rawProductDifference_eq_zero_of_notMem
  intro hxQ
  exact Set.disjoint_left.mp (hdis hS hR hSR)
    ((productBox_subset_iff Q S).mpr hQS hxQ) hx

theorem difference_forest_local_eq
    (T H : Finset (∀ i, Box (Fin (d i))))
    (hdis : Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (productBox R) (productBox S)))
    (hcover : ∀ Q ∈ H, ∃ R ∈ T, ∀ i, Q i ≤ R i)
    (F : boundedMeasurableFunctions d) (R : ∀ i, Box (Fin (d i))) (hR : R ∈ T)
    (x : ProductPoint d) (hx : x ∈ productBox R) :
    (∑ Q ∈ H.filter (fun Q => ∀ i, Q i ≤ R i),
      productDifferenceMap Finset.univ Q F).1 x =
        ∑ Q ∈ H, rawProductDifference Q F.1 x := by
  simp only [Submodule.coe_sum, Finset.sum_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Q hQ
  by_cases hQR : ∀ i, Q i ≤ R i
  · rw [ite_eq_left hQR]
    exact (congrFun (rawProductDifference_eq_productDifferenceMap Q F) x).symm
  · rw [ite_eq_right hQR]
    exact (raw_difference_zero_on_other_root T H hdis hcover F.1 R hR Q hQ hQR x hx).symm

theorem difference_square_forest_local_eq
    (T H : Finset (∀ i, Box (Fin (d i))))
    (hdis : Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (productBox R) (productBox S)))
    (hcover : ∀ Q ∈ H, ∃ R ∈ T, ∀ i, Q i ≤ R i)
    (f : ProductPoint d → ℝ) (R : ∀ i, Box (Fin (d i))) (hR : R ∈ T)
    (x : ProductPoint d) (hx : x ∈ productBox R) :
    finiteDifferenceSquare (H.filter (fun Q => ∀ i, Q i ≤ R i)) f x =
      finiteDifferenceSquare H f x := by
  apply congrArg Real.sqrt
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Q hQ
  by_cases hQR : ∀ i, Q i ≤ R i
  · rw [ite_eq_left hQR]
  · rw [ite_eq_right hQR,
      raw_difference_zero_on_other_root T H hdis hcover f R hR Q hQ hQR x hx]
    simp only [zero_pow (by decide : 2 ≠ 0)]

theorem difference_square_forest_integral_le
    (T H : Finset (∀ i, Box (Fin (d i))))
    (hdis : Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (productBox R) (productBox S)))
    (hcover : ∀ Q ∈ H, ∃ R ∈ T, ∀ i, Q i ≤ R i)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 0 < p) :
    (∑ R ∈ T, ∫ x in productBox R,
      Real.rpow (finiteDifferenceSquare (H.filter (fun Q => ∀ i, Q i ≤ R i)) f x) p) ≤
        ∫ x, Real.rpow (finiteDifferenceSquare H f x) p := by
  have hi := integrable_rpow_finiteDifferenceSquare H f p hp
  calc
    _ = ∑ R ∈ T, ∫ x in productBox R, Real.rpow (finiteDifferenceSquare H f x) p := by
      apply Finset.sum_congr rfl
      intro R hR
      apply setIntegral_congr_fun (measurableSet_productBox R)
      intro x hx
      exact congrArg (fun z : ℝ => Real.rpow z p)
        (difference_square_forest_local_eq T H hdis hcover f R hR x hx)
    _ = ∫ x in ⋃ R ∈ T, productBox R, Real.rpow (finiteDifferenceSquare H f x) p :=
      (integral_biUnion_finset T (fun R _ => measurableSet_productBox R) hdis
        (fun _ _ => hi.integrableOn)).symm
    _ ≤ _ := setIntegral_le_integral hi
      (Filter.Eventually.of_forall (fun _ => Real.rpow_nonneg (Real.sqrt_nonneg _) p))

end ReyZygmund.Geometry
