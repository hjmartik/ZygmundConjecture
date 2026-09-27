import ReyZygmund.Geometry.LeafAverages
import ReyZygmund.Maximal.Nonnegative
import ReyZygmund.Maximal.UpperExponent

/-! # Finite maximal estimates for integrable inputs

The finite maximum uses normalized integrals of `|f|`. The norm theorem assumes
that `f` and `|f|^p` are integrable on the top rectangle. Averaging `|f|` on the
smallest cubes preserves every selected average and reduces the estimate to the
bounded finite-input case.


-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- The finite-family maximum for a real function. Statements using
its integrals impose the required local integrability separately. -/
noncomputable def finiteFunctionMaximal
    (G : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ)
    (x : ProductPoint d) : ℝ :=
  if h : G.Nonempty then G.sup' h (fun Q =>
    (productBox Q).indicator
      (fun _ => (∫ y in productBox Q, |f y|) / volume.real (productBox Q)) x)
  else 0

theorem finiteFunctionMaximal_of_bounded
    (G : Finset (∀ i, Box (Fin (d i)))) (F : boundedMeasurableFunctions d) :
    finiteFunctionMaximal G F.1 = finiteFamilyMaximal G F := rfl

/-- Averaging `|f|` on the smallest cubes preserves its averages over all selected
rectangles, including at boundary points and for the empty family. -/
theorem finiteFunctionMaximal_leafAverage
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (f : ProductPoint d → ℝ) (hf : IntegrableOn f (productBox I) volume) :
    finiteFunctionMaximal G f = finiteFamilyMaximal G
      (finiteInput I N (leafAverage I N (fun x => |f x|))
        (productLeafConstant_leafAverage I N (fun x => |f x|))) := by
  let g := leafAverage I N (fun x => |f x|)
  have hg : ProductLeafConstant I N g := productLeafConstant_leafAverage I N _
  have hnonneg : ∀ x, 0 ≤ g x :=
    leafAverage_nonneg I N (fun x => |f x|) (fun x _ => abs_nonneg (f x))
  have heq : ∀ Q ∈ G,
      (∫ y in productBox Q, |(finiteInput I N g hg).1 y|) =
        ∫ y in productBox Q, |f y| := by
    intro Q hQ
    calc
      _ = ∫ y in productBox Q, g y := by
        apply setIntegral_congr_fun (measurableSet_productBox Q)
        intro y hy
        change |(productBox I).indicator g y| = g y
        rw [Set.indicator_of_mem (productBox_subset_root_of_mem_productDescendants
          (hG hQ) hy), abs_of_nonneg (hnonneg y)]
      _ = _ := integral_leafAverage_descendant I N Q (hG hQ) _ hf.abs
  funext x
  by_cases h : G.Nonempty
  · rw [finiteFunctionMaximal, dite_eq_left h, finiteFamilyMaximal, dite_eq_left h]
    apply Finset.sup'_congr _ rfl
    intro Q hQ
    rw [heq Q hQ]
  · simp only [finiteFunctionMaximal, finiteFamilyMaximal, dite_eq_right h]

/-- The finite incomparable estimate assumes integrability of the input and its
absolute p-th power on the top rectangle. The dimension-only factor is uniform in
the smallest scale, top rectangle, family, input and real exponent p > 1. -/
theorem finite_incomparable_general_input_norm
    (hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : IntegrableOn f (productBox I) volume)
    (hpow : IntegrableOn (fun x => Real.rpow |f x| p) (productBox I) volume) :
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFunctionMaximal G f x) p) (1 / p) ≤
      (maximalDimensionConstant d + 3) * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow |f x| p) (1 / p) := by
  let g := leafAverage I N (fun x => |f x|)
  have hg : ProductLeafConstant I N g := productLeafConstant_leafAverage I N _
  have hnonneg : ∀ x, 0 ≤ g x :=
    leafAverage_nonneg I N (fun x => |f x|) (fun x _ => abs_nonneg (f x))
  let F := finiteInput I N g hg
  have hF : ProductLeafConstant I N F.1 := productLeafConstant_indicator hg
  have hs : ∀ x, x ∉ productBox I → F.1 x = 0 :=
    fun x hx => Set.indicator_of_notMem hx g
  have hpower : (∫ x in productBox I, Real.rpow (g x) p) ≤
      ∫ x in productBox I, Real.rpow |f x| p := by
    have h := integral_abs_rpow_leafAverage_le I N (fun x => |f x|) p hp.le hf.abs
      (by simpa only [abs_abs] using hpow)
    simpa only [g, abs_abs, abs_of_nonneg (hnonneg _)] using h
  have hnorm : Real.rpow (∫ x in productBox I, Real.rpow (g x) p) (1 / p) ≤
      Real.rpow (∫ x in productBox I, Real.rpow |f x| p) (1 / p) :=
    Real.rpow_le_rpow (integral_nonneg (fun x => Real.rpow_nonneg (hnonneg x) p))
      hpower (one_div_nonneg.mpr (zero_lt_one.trans hp).le)
  have hK : 0 ≤ maximalDimensionConstant d := by
    unfold maximalDimensionConstant
    exact sq_nonneg _
  have hC : 0 ≤ (p / (p - 1)) ^ (m - 1) :=
    pow_nonneg (div_nonneg (zero_lt_one.trans hp).le (sub_pos.mpr hp).le) _
  have hY : 0 ≤ Real.rpow (∫ x in productBox I, Real.rpow (g x) p) (1 / p) :=
    Real.rpow_nonneg (integral_nonneg (fun x => Real.rpow_nonneg (hnonneg x) p)) _
  rw [finiteFunctionMaximal_leafAverage I N G hG f hf]
  have hfinite : Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal G F x) p) (1 / p) ≤
      (maximalDimensionConstant d + 3) * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow (g x) p) (1 / p) := by
    by_cases hp3 : p ≤ (3 : ℝ) / 2
    · exact (finite_incomparable_maximal_norm_nonneg hm I N hd G hG hinc
        g hg (fun x _ => hnonneg x) p hp hp3).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num)) hC) hY)
    · have hu := finite_family_maximal_norm_upper (by omega) I N G hG hd F hF hs
        p (le_of_not_ge hp3)
      have hFu : (∫ x in productBox I, Real.rpow |F.1 x| p) =
          ∫ x in productBox I, Real.rpow (g x) p := by
        apply setIntegral_congr_fun (measurableSet_productBox I)
        intro x hx
        change Real.rpow |(productBox I).indicator g x| p = Real.rpow (g x) p
        rw [Set.indicator_of_mem hx, abs_of_nonneg (hnonneg x)]
      rw [hFu] at hu
      exact hu.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK) hC) hY)
  exact hfinite.trans (mul_le_mul_of_nonneg_left hnorm
    (mul_nonneg (add_nonneg hK (by norm_num)) hC))

end ReyZygmund
