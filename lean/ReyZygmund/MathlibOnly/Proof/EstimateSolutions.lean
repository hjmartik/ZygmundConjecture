import ReyZygmund.ToMathlib.MeasureTheory.Exponential
import ReyZygmund.MathlibOnly.Proof.EstimateStatements
import ReyZygmund.MathlibOnly.Proof.IncomparabilityBridge
import ReyZygmund.MathlibOnly.Proof.MeasureBridge
import ReyZygmund.MathlibOnly.Proof.OperatorBridge
import ReyZygmund.Maximal.WeakerGlobal
import ReyZygmund.Overlap.Exponential
import ReyZygmund.Continuous.Endpoint
import ReyZygmund.Main.Endpoints
import ReyZygmund.Main.PhiSparse
import ReyZygmund.Main.Sharpness

/-!
# Proofs of the real-valued estimates

The maximal theorem follows from the finite-family estimate and the passage to general dyadic families.
The overlap theorem uses the resulting moment bounds and the paper's tail and layer-cake argument.
Adding the shadow measure converts the exponential-minus-one estimate to the stated exponential bound.
The remaining four results use the continuous, rounded, sparse-Phi and
sharpness theorems. The public proofs express these conclusions using
extended norms and exponential integrals.
-/

open BoxIntegral MeasureTheory Filter
open scoped BigOperators ENNReal Classical Topology

namespace ReyZygmund.MathlibOnly.Proof.Estimates

private theorem weak_incomparability_transfer {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i)))) (hweak : WeaklyIncomparable G) :
    ∀ R ∈ G, ∀ S ∈ G, Geometry.productRectangle R ⊆ Geometry.productRectangle S →
      ∃ i, R i = S i := by
  intro R hR S hS hRS
  exact (Geometry.weaklyIncomparable_iff_equal_factor G).mp hweak R hR S hS
    ((Geometry.productRectangle_subset_iff R S).mp hRS)

/-- The maximal estimate obtained from finite families by countable exhaustion. -/
theorem weakly_incomparable_maximal : WeaklyIncomparableMaximal := by
  refine ⟨Overlap.momentConstant, Overlap.momentConstant_pos, ?_⟩
  intro m d hm hd D G hG hweak p hp _hp2 f hf
  have hweak' := weak_incomparability_transfer G hweak
  rw [maximal_eq_euclidean_of_memLp G f p hp hf]
  refine ⟨euclidean_weaker_grid_maximal_ae_finite hm hd D
    G hG hweak' f p hp hf, ?_⟩
  simpa only [Overlap.momentConstant_eq] using
    euclidean_weaker_grid_maximal_eLpNorm hm hd D
      G hG hweak' f p hp hf

/-- The overlap estimate: moments followed by Chebyshev and layer cake. -/
theorem weakly_incomparable_overlap : WeaklyIncomparableOverlap := by
  obtain ⟨c, B, hc, hB, hexponential⟩ := Overlap.weaker_sparse_overlap_exponential
  let C (m D : ℕ) := Overlap.momentConstant m D + B m D + 1
  have hC (m D) : 0 < C m D := by
    exact add_pos (add_pos (Overlap.momentConstant_pos m D) (hB m D)) zero_lt_one
  refine ⟨C, c, hC, hc, ?_⟩
  intro m d hm hd D G hG hweak eta heta _heta1 hs hv
  have hweak' := weak_incomparability_transfer G hweak
  obtain ⟨E, hE, hEdis⟩ := hs
  have hEmeas := fun R hR => (hE R hR).1
  have hEsub := fun R hR => (hE R hR).2.1
  have hEmass := fun R hR => (hE R hR).2.2
  simp only [Geometry.rectangle_eq_flatProductBox] at hEsub hEmass
  rw [shadow_eq] at hv
  rw [overlap_eq, shadow_eq]
  refine ⟨Overlap.weaker_sparse_overlap_ae_finite hm hd D
    G hG hweak' eta heta E hEmeas hEsub hEdis hEmass hv, ?_, ?_⟩
  · intro q hq
    have hmoment := Overlap.weaker_sparse_overlap_eLpNorm hm hd
      D G hG hweak' eta heta E hEmeas hEsub hEdis hEmass hv q hq
    rw [← Overlap.momentConstant_eq d] at hmoment
    apply hmoment.trans
    apply mul_le_mul' ?_ le_rfl
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr heta.le))
      (pow_nonneg (by linarith) _)
    dsimp only [C]
    linarith [hB m (∑ i, d i)]
  · have hexp := hexponential m d hm hd D G hG hweak'
      eta heta E hEmeas hEsub hEdis hEmass hv
    simp_rw [ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_one] at hexp
    have hfull := lintegral_exp_le_add_one volume (Overlap.shadow G)
      (fun x => c m (∑ i, d i) *
        Real.rpow (eta * (Overlap.overlap G x).toReal) (1 / ((m - 1 : ℕ) : ℝ)))
      (fun x => mul_nonneg (hc _ _).le
        (Real.rpow_nonneg (mul_nonneg heta.le ENNReal.toReal_nonneg) _))
      (B m (∑ i, d i)) (hB _ _).le hexp
    apply hfull.trans
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    dsimp only [C]
    linarith [Overlap.momentConstant_pos m (∑ i, d i)]

theorem continuous_endpoint : ContinuousEndpoint := by
  intro n totalDim hn
  obtain ⟨C, hC, h⟩ := Continuous.continuous_endpoint_theorem n totalDim hn
  refine ⟨C, hC, ?_⟩
  intro d hd hdim phi hphi f hf lam hlam
  rw [maximal_eq_euclidean_of_locallyIntegrable _ f hf]
  exact h d hd hdim phi hphi f hf lam hlam

theorem rounded_endpoint : RoundedEndpoint := by
  intro n totalDim hn
  obtain ⟨C, hC, h⟩ := Main.rounded_endpoint_theorem n totalDim hn
  refine ⟨C, hC, ?_⟩
  intro d hd hdim phi hphi tau f hf lam hlam
  rw [rounded_levelset_measure_eq tau phi f hf lam, roundedRectangles_eq,
    maximal_eq_euclidean_of_locallyIntegrable _ f hf]
  exact h d hd hdim phi hphi tau f hf lam hlam

theorem phi_sparse_overlap : PhiSparseOverlap := by
  intro n totalDim hn eta heta heta1
  obtain ⟨c, C, hc, hC, h⟩ := Main.phi_sparse_overlap_theorem n totalDim hn eta heta heta1
  refine ⟨c, C + 1, hc, (by linarith), ?_⟩
  intro d hd hdim D Phi hPhi G hG hs hv
  obtain ⟨hfinite, hexp⟩ := h d hd hdim D Phi hPhi G hG hs hv
  refine ⟨hfinite, ?_⟩
  exact lintegral_exp_le_add_one volume (shadow G)
    (fun x => c * Real.rpow (overlap G x).toReal (1 / (n : ℝ)))
    (fun x => mul_nonneg hc.le (Real.rpow_nonneg ENNReal.toReal_nonneg _)) C hC.le hexp

theorem phi_sparse_sharpness : PhiSparseSharpness := by
  intro n hn d hd D eta heta heta1
  obtain ⟨G, hG, hlim⟩ := Main.phi_sparse_sharpness_theorem n hn d hd D eta heta heta1
  refine ⟨G, ?_, ?_⟩
  · intro N hN
    obtain ⟨hfamily, hincomparable, hsparse, hshadow⟩ := hG N hN
    exact ⟨hfamily, hincomparable, hsparse, hshadow⟩
  intro c beta hc hbeta
  have hbeta0 : 0 < beta := (one_div_pos.mpr (by positivity : 0 < (n : ℝ))).trans hbeta
  apply (tendsto_overlap_exponential_iff G c beta hc hbeta0).mp
  apply tendsto_nhds_top_mono' (hlim c beta hc hbeta)
  intro N
  apply lintegral_mono
  intro x
  exact tsub_le_self

end ReyZygmund.MathlibOnly.Proof.Estimates
