import ReyZygmund.Maximal.Euclidean

/-! # Finite-family maxima in Euclidean coordinates

For a finite family, the extended supremum equals the embedded real maximum and is
finite everywhere. Local integrability is still required when interpreting the
real integral coefficients as averages.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

theorem familyMaximal_coe_finset
    (G : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ)
    (x : ProductPoint d) :
    familyMaximal (G : Set _) f x = ENNReal.ofReal (finiteFunctionMaximal G f x) := by
  apply le_antisymm
  · apply iSup_le
    intro Q
    exact ENNReal.ofReal_le_ofReal
      (positiveMean_le_finiteFunctionMaximal G f Q.1 Q.2 x)
  · by_cases h : G.Nonempty
    · obtain ⟨Q, hQ, hmax⟩ := Finset.exists_mem_eq_sup' h
        (fun Q => (productBox Q).indicator
          (fun _ => (∫ y in productBox Q, |f y|) / volume.real (productBox Q)) x)
      rw [finiteFunctionMaximal, dite_eq_left h, hmax]
      exact le_iSup (fun Q : (G : Set _) => ENNReal.ofReal ((productBox Q.1).indicator
        (fun _ => (∫ y in productBox Q.1, |f y|) / volume.real (productBox Q.1)) x)) ⟨Q, hQ⟩
    · rw [finiteFunctionMaximal, dite_eq_right h, ENNReal.ofReal_zero]
      exact zero_le

theorem euclideanFamilyMaximal_coe_finset
    (G : Finset (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (x : Fin (∑ i, d i) → ℝ) :
    euclideanFamilyMaximal (G : Set _) f x = ENNReal.ofReal
      (finiteFunctionMaximal G (fun y => f (flattenCoordinates d y))
        ((flattenCoordinates d).symm x)) := by
  simpa only [MeasurableEquiv.apply_symm_apply] using
    (euclideanFamilyMaximal_flatten (G : Set _) f ((flattenCoordinates d).symm x)).trans
      (familyMaximal_coe_finset G _ _)

theorem euclideanFamilyMaximal_finset_lt_top
    (G : Finset (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (x : Fin (∑ i, d i) → ℝ) :
    euclideanFamilyMaximal (G : Set _) f x < ∞ := by
  rw [euclideanFamilyMaximal_coe_finset]
  exact ENNReal.ofReal_lt_top

theorem integrable_euclideanFamilyMaximal_finset
    (G : Finset (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) :
    Integrable (fun x => (euclideanFamilyMaximal (G : Set _) f x).toReal) volume := by
  have hmeas := (measurable_euclideanFamilyMaximal (G : Set _) G.countable_toSet f).ennreal_toReal
  apply ((volume_preserving_flattenCoordinates d).integrable_comp hmeas.aestronglyMeasurable).mp
  have hi := integrable_rpow_finiteFunctionMaximal G
    (fun y => f (flattenCoordinates d y)) 1 (by norm_num)
  change Integrable (fun x =>
    (euclideanFamilyMaximal (G : Set _) f (flattenCoordinates d x)).toReal) volume
  simp_rw [euclideanFamilyMaximal_flatten, familyMaximal_coe_finset,
    ENNReal.toReal_ofReal (finiteFunctionMaximal_nonneg _ _ _)]
  simpa only [Real.rpow_eq_pow, Real.rpow_one] using hi

end ReyZygmund
