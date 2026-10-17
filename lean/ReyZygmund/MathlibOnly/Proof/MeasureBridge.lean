import ReyZygmund.MathlibOnly.Proof.Definitions
import ReyZygmund.MathlibOnly.Proof.OverlapBridge
import ReyZygmund.MathlibOnly.Proof.BoundaryBridge
import ReyZygmund.Sharpness.FiniteIntegral

/-!
# Boundary conventions and real integrals

The rounded maximal operator uses the paper's lower-inclusive convention.
For finite families, the full overlap exponential is integrable, so its real
integral agrees with the nonnegative integral used in the sharpness proof.
-/

open BoxIntegral MeasureTheory Filter
open scoped BigOperators ENNReal Classical Topology

namespace ReyZygmund.MathlibOnly.Proof.Estimates

variable {m : ℕ} {d : Fin m → ℕ}

theorem rectangleIco_eq (R : ∀ i, Box (Fin (d i))) :
    rectangleIco R = Continuous.icoFlatProductBox R := by
  ext x
  simp only [rectangleIco, Continuous.icoFlatProductBox, Set.mem_ofPred_eq,
    Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ico]
  constructor
  · intro h j
    obtain ⟨⟨i, k⟩, rfl⟩ := finSigmaFinEquiv.surjective j
    simpa only [Geometry.flatProductBox, Geometry.flattenCoordinates_apply] using h i k
  · intro h i k
    simpa only [Geometry.flatProductBox, Geometry.flattenCoordinates_apply] using
      h (finSigmaFinEquiv ⟨i, k⟩)

/-- Local integrability identifies the explicit nonnegative averages with real averages. -/
theorem maximalIco_eq (G : Set (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf : LocallyIntegrable f volume) :
    maximalIco G f = Continuous.icoEuclideanFamilyMaximal G f := by
  rw [maximalIco_eq_iSup_indicator]
  funext x
  unfold Continuous.icoEuclideanFamilyMaximal
  congr 1
  funext R
  rw [rectangleIco_eq]
  obtain ⟨hvpos, hv⟩ := Continuous.icoFlatProductBox_volume_pos_finite R.1
  have hlocal := Continuous.integrableOn_icoFlatProductBox R.1 f hf
  by_cases hx : x ∈ Continuous.icoFlatProductBox R.1
  · simp only [Set.indicator_of_mem hx]
    rw [ENNReal.ofReal_div_of_pos hvpos,
      ofReal_integral_eq_lintegral_ofReal hlocal.abs
        (Eventually.of_forall (fun y => abs_nonneg (f y))),
      Measure.real, ENNReal.ofReal_toReal hv.ne]
  · simp only [Set.indicator_of_notMem hx, ENNReal.ofReal_zero]

theorem rounded_levelset_measure_eq {n : ℕ} {d : Fin (n + 1) → ℕ}
    (tau : ∀ i, Fin (d i) → Fin 3)
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf : LocallyIntegrable f volume) (lam : ℝ) :
    volume {x | ENNReal.ofReal lam < maximalIco (roundedRectangles tau phi) f x} =
      volume {x | ENNReal.ofReal lam < maximal (roundedRectangles tau phi) f x} := by
  rw [maximalIco_eq _ f hf]
  apply measure_congr
  apply eventuallyEqSet_iff.mpr
  filter_upwards [rounded_maximal_ae_eq_ico tau phi f hf] with x hx
  rw [hx]

/-- A finite family has bounded overlap and finite shadow, hence an integrable exponential. -/
theorem integrableOn_overlap_exponential (H : Finset (∀ i, Box (Fin (d i))))
    (c beta : ℝ) (hc : 0 < c) (hbeta : 0 < beta) :
    IntegrableOn (fun x => Real.exp (c * Real.rpow
      (overlap (H : Set (∀ i, Box (Fin (d i)))) x).toReal beta))
      (shadow (H : Set (∀ i, Box (Fin (d i))))) volume := by
  rw [shadow_eq, overlap_eq, Overlap.shadow_finset]
  have h := Sharpness.integrableOn_overlap_finset_exponential H c beta hc hbeta
  rw [Overlap.shadow_finset] at h
  have hfinite : IsFiniteMeasure (volume.restrict (Overlap.finiteShadow H)) :=
    ⟨by simpa using Overlap.volume_finiteShadow_lt_top H⟩
  have hone : IntegrableOn (fun _ : Fin (∑ i, d i) → ℝ => (1 : ℝ))
      (Overlap.finiteShadow H) volume := integrable_const 1
  convert h.add hone using 1
  ext x
  simp only [Pi.add_apply, sub_add_cancel]

theorem lintegral_overlap_exponential_eq (H : Finset (∀ i, Box (Fin (d i))))
    (c beta : ℝ) (hc : 0 < c) (hbeta : 0 < beta) :
    (∫⁻ x in shadow (H : Set (∀ i, Box (Fin (d i)))), ENNReal.ofReal
      (Real.exp (c * Real.rpow (overlap (H : Set (∀ i, Box (Fin (d i)))) x).toReal beta))) =
    ENNReal.ofReal (∫ x in shadow (H : Set (∀ i, Box (Fin (d i)))),
      Real.exp (c * Real.rpow (overlap (H : Set (∀ i, Box (Fin (d i)))) x).toReal beta)) :=
  (ofReal_integral_eq_lintegral_ofReal (integrableOn_overlap_exponential H c beta hc hbeta)
    (Eventually.of_forall (fun _ => (Real.exp_pos _).le))).symm

theorem tendsto_overlap_exponential_iff (G : ℕ → Finset (∀ i, Box (Fin (d i))))
    (c beta : ℝ) (hc : 0 < c) (hbeta : 0 < beta) :
    Tendsto (fun N => ∫⁻ x in shadow (G N : Set (∀ i, Box (Fin (d i)))), ENNReal.ofReal
      (Real.exp (c * Real.rpow (overlap (G N : Set (∀ i, Box (Fin (d i)))) x).toReal beta)))
      atTop (𝓝 ∞) ↔
    Tendsto (fun N => ∫ x in shadow (G N : Set (∀ i, Box (Fin (d i)))),
      Real.exp (c * Real.rpow (overlap (G N : Set (∀ i, Box (Fin (d i)))) x).toReal beta))
      atTop atTop := by
  simp_rw [lintegral_overlap_exponential_eq _ c beta hc hbeta]
  exact ENNReal.tendsto_ofReal_nhds_top

end ReyZygmund.MathlibOnly.Proof.Estimates
