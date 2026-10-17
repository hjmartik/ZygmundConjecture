import ReyZygmund.MathlibOnly.Definitions
import ReyZygmund.MathlibOnly.Proof.MeasureBridge
import ReyZygmund.ToMathlib.MeasureTheory.LpSeminorm

/-!
# Real and extended forms of norms and exponential integrals

Almost-everywhere finiteness identifies the extended norms and exponential
integrals with the real-valued quantities used in the analytic proofs.
-/

open BoxIntegral MeasureTheory Filter
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.MathlibOnly

noncomputable section

theorem exp_ofReal {t : ℝ} (ht : 0 ≤ t) :
    exp (ENNReal.ofReal t) = ENNReal.ofReal (Real.exp t) := by
  simp only [exp, EReal.coe_ennreal_ofReal, max_eq_left (by exact_mod_cast ht),
    EReal.exp_coe]

/-- For finite nonnegative inputs the extended power and exponential agree
with the real expressions used in the overlap proof. -/
theorem exp_mul_rpow_eq {t : ℝ≥0∞} (ht : t < ∞)
    {c a beta : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hbeta : 0 ≤ beta) :
    exp (ENNReal.ofReal c * (ENNReal.ofReal a * t) ^ beta) =
      ENNReal.ofReal (Real.exp (c * Real.rpow (a * t.toReal) beta)) := by
  have hbase : ENNReal.ofReal a * t = ENNReal.ofReal (a * t.toReal) := by
    rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_toReal ht.ne]
  rw [hbase, ENNReal.ofReal_rpow_of_nonneg
    (mul_nonneg ha ENNReal.toReal_nonneg) hbeta,
    ← ENNReal.ofReal_mul hc]
  exact exp_ofReal (mul_nonneg hc (Real.rpow_nonneg
    (mul_nonneg ha ENNReal.toReal_nonneg) _))

theorem lintegral_exp_mul_rpow_eq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (s : Set α) {f : α → ℝ≥0∞}
    (hf : ∀ᵐ x ∂μ, f x < ∞) {c a beta : ℝ}
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hbeta : 0 ≤ beta) :
    (∫⁻ x in s, exp (ENNReal.ofReal c * (ENNReal.ofReal a * f x) ^ beta) ∂μ) =
      ∫⁻ x in s, ENNReal.ofReal (Real.exp (c * Real.rpow (a * (f x).toReal) beta))
        ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hf] with x hx
  exact exp_mul_rpow_eq hx hc ha hbeta

/-- For finite families, the real overlap is exactly the finite indicator sum. -/
theorem overlap_toReal_finset {m : ℕ} {d : Fin m → ℕ}
    (G : Finset (Rectangle d)) (x : Point d) :
    (overlap (G : Set (Rectangle d)) x).toReal =
      ∑ R ∈ G, (rectangle R).indicator (fun _ => (1 : ℝ)) x := by
  rw [Proof.Estimates.overlap_eq, Overlap.toReal_overlap_finset]
  simp only [Overlap.finiteOverlap, ← Geometry.rectangle_eq_flatProductBox]

end
end ReyZygmund.MathlibOnly
