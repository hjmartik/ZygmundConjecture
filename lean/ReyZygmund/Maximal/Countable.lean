import ReyZygmund.Maximal.Forest
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Countable limits of finite-family maxima

The supremum uses the same normalized integrals of absolute values as
`finiteFunctionMaximal`. Local integrability is needed to interpret these real
integral expressions as averages. Under uniform estimates on finite subfamilies,
monotone convergence gives the extended-integral bound for the countable family.


-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- The extended-valued maximum over a family of product boxes. -/
noncomputable def familyMaximal
    (G : Set (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ)
    (x : ProductPoint d) : ℝ≥0∞ :=
  ⨆ Q : G, ENNReal.ofReal ((productBox Q.1).indicator
    (fun _ => (∫ y in productBox Q.1, |f y|) / volume.real (productBox Q.1)) x)

/-- Countable families give measurable extended-valued maxima, even when the
input has no regularity. Each totalized integral is a scalar coefficient. -/
theorem measurable_familyMaximal
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G.Countable)
    (f : ProductPoint d → ℝ) : Measurable (familyMaximal G f) := by
  have := hG.to_subtype
  exact Measurable.iSup (fun Q : G =>
    ((measurable_const : Measurable (fun _ : ProductPoint d =>
      (∫ y in productBox Q.1, |f y|) / volume.real (productBox Q.1))).indicator
        (measurableSet_productBox Q.1)).ennreal_ofReal)

private theorem finiteFunctionMaximal_le_familyMaximal
    (G : Set (∀ i, Box (Fin (d i)))) (H : Finset G)
    (f : ProductPoint d → ℝ) (x : ProductPoint d) :
    ENNReal.ofReal (finiteFunctionMaximal (H.image Subtype.val) f x) ≤
      familyMaximal G f x := by
  by_cases h : (H.image Subtype.val).Nonempty
  · obtain ⟨Q, hQ, hmax⟩ := Finset.exists_mem_eq_sup' h
      (fun Q => (productBox Q).indicator
        (fun _ => (∫ y in productBox Q, |f y|) / volume.real (productBox Q)) x)
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hQ
    rw [finiteFunctionMaximal, dite_eq_left h, hmax]
    exact le_iSup (fun Q : G => ENNReal.ofReal ((productBox Q.1).indicator
      (fun _ => (∫ y in productBox Q.1, |f y|) / volume.real (productBox Q.1)) x)) R
  · rw [finiteFunctionMaximal, dite_eq_right h, ENNReal.ofReal_zero]
    exact zero_le

/-- The family maximum is exactly the supremum of its finite maxima.
This pointwise identity needs no countability assumption and includes empty
families and empty finite subfamilies. -/
theorem familyMaximal_eq_iSup_finset
    (G : Set (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ)
    (x : ProductPoint d) :
    familyMaximal G f x = ⨆ H : Finset G,
      ENNReal.ofReal (finiteFunctionMaximal (H.image Subtype.val) f x) := by
  apply le_antisymm
  · apply iSup_le
    intro Q
    apply le_iSup_of_le ({Q} : Finset G)
    exact ENNReal.ofReal_le_ofReal (positiveMean_le_finiteFunctionMaximal
      (({Q} : Finset G).image Subtype.val) f Q.1
      (Finset.mem_image.mpr ⟨Q, Finset.mem_singleton_self Q, rfl⟩) x)
  · exact iSup_le (fun H => finiteFunctionMaximal_le_familyMaximal G H f x)

/-- Directed monotone convergence for positive real powers of the
finite-family maxima. Values and integrals may equal infinity. -/
theorem lintegral_familyMaximal_rpow_eq_iSup
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G.Countable)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 0 < p) :
    (∫⁻ x, (familyMaximal G f x) ^ p) =
      ⨆ H : Finset G, ∫⁻ x,
        (ENNReal.ofReal (finiteFunctionMaximal (H.image Subtype.val) f x)) ^ p := by
  have := hG.to_subtype
  let F (H : Finset G) (x : ProductPoint d) : ℝ≥0∞ :=
    (ENNReal.ofReal (finiteFunctionMaximal (H.image Subtype.val) f x)) ^ p
  have hmeas (H : Finset G) : Measurable (F H) :=
    (measurable_finiteFunctionMaximal (H.image Subtype.val) f).ennreal_ofReal.pow_const p
  have hmono : Monotone F := by
    intro H K hHK x
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
      (finiteFunctionMaximal_mono _ _ (Finset.image_mono Subtype.val hHK) f x)) hp.le
  have hdir : Directed (· ≤ ·) F := by
    intro H K
    exact ⟨H ∪ K, hmono Finset.subset_union_left, hmono Finset.subset_union_right⟩
  have heq (x : ProductPoint d) : (familyMaximal G f x) ^ p =
      ⨆ H : Finset G, F H x := by
    rw [familyMaximal_eq_iSup_finset]
    exact (ENNReal.orderIsoRpow p hp).map_iSup
      (fun H : Finset G =>
        ENNReal.ofReal (finiteFunctionMaximal (H.image Subtype.val) f x))
  calc
    _ = ∫⁻ x, ⨆ H : Finset G, F H x := lintegral_congr heq
    _ = ⨆ H : Finset G, ∫⁻ x, F H x :=
      lintegral_iSup_directed_of_measurable hmeas hdir

/-- Any uniform extended power-integral bound for all finite subfamilies
passes to the countable family. This is a limit implication, not a maximal
inequality supplied without its finite hypotheses. -/
theorem lintegral_familyMaximal_rpow_le
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G.Countable)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 0 < p) (C : ℝ≥0∞)
    (hfinite : ∀ H : Finset G, (∫⁻ x,
      (ENNReal.ofReal (finiteFunctionMaximal (H.image Subtype.val) f x)) ^ p) ≤ C) :
    (∫⁻ x, (familyMaximal G f x) ^ p) ≤ C := by
  rw [lintegral_familyMaximal_rpow_eq_iSup G hG f p hp]
  exact iSup_le hfinite

end ReyZygmund
