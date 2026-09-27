import ReyZygmund.Maximal.Signed
import Mathlib.Data.Finset.Interval

/-! # Signed maximal functions in selected coordinates

Only coordinates in `A` are averaged. Unused entries of a descendant tuple repeat
the same candidate and introduce no counting factor. For inputs constant on the
smallest cubes, choosing a smallest cube in an additional averaged coordinate
preserves the previous value.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- The maximum of absolute signed averages in the selected coordinates. -/
noncomputable def finiteSignedPartialMaximal
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A : Finset (Fin m)) (F : boundedMeasurableFunctions d)
    (x : ProductPoint d) : ℝ :=
  (productDescendants I N).sup' ⟨I, root_mem_productDescendants I N⟩
    (fun Q => |(productAverageMap A Q F).1 x|)

theorem finiteSignedPartialMaximal_nonneg
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A : Finset (Fin m)) (F : boundedMeasurableFunctions d) (x : ProductPoint d) :
    0 ≤ finiteSignedPartialMaximal I N A F x :=
  (abs_nonneg _).trans (Finset.le_sup'
    (fun Q => |(productAverageMap A Q F).1 x|)
    (root_mem_productDescendants I N))

@[simp] theorem finiteSignedPartialMaximal_univ
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) :
    finiteSignedPartialMaximal I N Finset.univ F = finiteSignedProductMaximal I N F := rfl

@[simp] theorem finiteSignedPartialMaximal_empty
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) :
    finiteSignedPartialMaximal I N ∅ F x = |F.1 x| := by
  apply Finset.sup'_eq_of_forall
  intro Q _
  simp

theorem measurable_finiteSignedPartialMaximal
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A : Finset (Fin m)) (F : boundedMeasurableFunctions d) :
    Measurable (finiteSignedPartialMaximal I N A F) := by
  have h := Finset.measurable_sup' (s := productDescendants I N)
    ⟨I, root_mem_productDescendants I N⟩
    (fun Q _ => (productAverageMap A Q F).2.1.norm)
  convert h using 1
  funext x
  simp only [finiteSignedPartialMaximal, Real.norm_eq_abs]
  exact (Finset.sup'_apply (C := fun _ : ProductPoint d => ℝ)
    ⟨I, root_mem_productDescendants I N⟩
    (fun Q y => |(productAverageMap A Q F).1 y|) x).symm

theorem productLeafConstant_finiteSignedPartialMaximal
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A : Finset (Fin m)) (F : boundedMeasurableFunctions d)
    (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) :
    ProductLeafConstant I N (finiteSignedPartialMaximal I N A F) := by
  intro P hP x hx y hy
  apply Finset.sup'_congr _ rfl
  intro Q hQ
  exact congrArg abs ((productAverageMap_productStep_closure I N F hf hs A Q
    (fun i _ => mem_productDescendants.mp hQ i)).1 P hP x hx y hy)

/-- Subadditivity uses signed linearity before taking absolute values. -/
theorem finiteSignedPartialMaximal_add_le
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A : Finset (Fin m)) (F G : boundedMeasurableFunctions d) (x : ProductPoint d) :
    finiteSignedPartialMaximal I N A (F + G) x ≤
      finiteSignedPartialMaximal I N A F x + finiteSignedPartialMaximal I N A G x := by
  apply Finset.sup'_le
  intro Q hQ
  change |(productAverageMap A Q (F + G)).1 x| ≤ _
  rw [map_add]
  change |(productAverageMap A Q F).1 x + (productAverageMap A Q G).1 x| ≤ _
  exact (abs_add_le _ _).trans (add_le_add
    (Finset.le_sup' (fun R => |(productAverageMap A R F).1 x|) hQ)
    (Finset.le_sup' (fun R => |(productAverageMap A R G).1 x|) hQ))

private theorem average_at_product_leaf
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (P : ∀ i, Box (Fin (d i))) (hP : P ∈ productLeaves I N)
    (j : Fin m) (x : ProductPoint d) (hx : x ∈ productBox P) :
    (averageMap j (P j) F).1 x = F.1 x := by
  rw [averageMap_apply, coordinateAverage_of_mem j (P j) F.1 x
    ((mem_productBox P x).mp hx j)]
  have heq : (∫ y in (P j : Set (Fin (d j) → ℝ)), F.1 (Function.update x j y)) =
      ∫ _ in (P j : Set (Fin (d j) → ℝ)), F.1 x := by
    apply setIntegral_congr_fun (P j).measurableSet_coe
    intro y hy
    apply hf P hP _ ?_ x hx
    apply (mem_productBox P _).mpr
    intro i
    by_cases hij : i = j
    · subst i
      simpa using hy
    · simpa [hij] using (mem_productBox P x).mp hx i
  rw [heq]
  simp only [integral_const, smul_eq_mul]
  simpa only [Measure.real, Measure.restrict_apply_univ] using
    mul_div_cancel_left₀ (F.1 x) (box_volume_pos (P j)).ne'

private theorem productAverageMap_congr_selected
    (A : Finset (Fin m)) (Q R : ∀ i, Box (Fin (d i)))
    (h : ∀ i ∈ A, Q i = R i) : productAverageMap A Q = productAverageMap A R := by
  apply Finset.noncommProd_congr rfl
  intro i hi
  rw [h i hi]

/-- The smallest cubes let the larger signed maximum recover every average
in fewer coordinates, including the case of no averaging at all. -/
theorem finiteSignedPartialMaximal_mono
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (B A : Finset (Fin m)) (hBA : B ⊆ A)
    (x : ProductPoint d) (hx : x ∈ productBox I) :
    finiteSignedPartialMaximal I N B F x ≤ finiteSignedPartialMaximal I N A F x := by
  have hm : Monotone (fun S => finiteSignedPartialMaximal I N S F x) := by
    apply Finset.monotone_iff_forall_le_insert.mpr
    intro S j hj
    apply Finset.sup'_le
    intro Q hQ
    obtain ⟨P, hP, hxP⟩ := productLeaves_cover I N x hx
    let R := Function.update Q j (P j)
    have hR : R ∈ productDescendants I N := by
      apply mem_productDescendants.mpr
      intro i
      by_cases hij : i = j
      · subst i
        simpa only [R, Function.update_self] using
          leaves_subset_descendants (I j) (N j) (Fintype.mem_piFinset.mp hP j)
      · simpa only [R, Function.update_of_ne hij] using mem_productDescendants.mp hQ i
    have hmap : productAverageMap S R = productAverageMap S Q := by
      apply productAverageMap_congr_selected
      intro i hi
      exact Function.update_of_ne (ne_of_mem_of_not_mem hi hj) _ _
    have hc := (productAverageMap_productStep_closure I N F hf hs S Q
      (fun i _ => mem_productDescendants.mp hQ i)).1
    have heq : (productAverageMap (insert j S) R F).1 x =
        (productAverageMap S Q F).1 x := by
      rw [productAverageMap_insert S j hj, Module.End.mul_apply, hmap]
      rw [show R j = P j by simp only [R, Function.update_self]]
      exact average_at_product_leaf I N _ hc P hP j x hxP
    rw [← heq]
    exact Finset.le_sup' (fun T => |(productAverageMap (insert j S) T F).1 x|) hR
  exact hm hBA

end ReyZygmund
