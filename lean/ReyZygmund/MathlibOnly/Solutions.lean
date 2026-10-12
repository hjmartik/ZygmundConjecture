import ReyZygmund.MathlibOnly.Statements
import ReyZygmund.MathlibOnly.Representation
import ReyZygmund.MathlibOnly.Proof.EstimateSolutions

/-!
# Proofs of the six independent statements

The analytic estimates are proved in the supporting library. The identities in
`Representation.lean` express their conclusions directly in the independent
definitions, including the extended norms and exponential integrals.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Classical Topology

namespace ReyZygmund.MathlibOnly

/-- The weakly incomparable maximal estimate. -/
theorem weakly_incomparable_maximal : WeaklyIncomparableMaximal := by
  intro m totalDim hm
  obtain ⟨C, hC, h⟩ := Proof.Estimates.weakly_incomparable_maximal
  refine ⟨C m totalDim, hC m totalDim, ?_⟩
  intro d hd hdim D G hG hweak p hp hp2 f hf
  obtain ⟨hfinite, hbound⟩ := h m d hm hd (fun i => (D i).toProof) G hG
    ((weaklyIncomparable_iff_proof G).mp hweak) p hp hp2 f hf
  rw [maximal_eq_proof, eLpNorm_eq_toReal _ hfinite]
  simpa only [hdim] using hbound

/-- The moment and exponential overlap bounds for sparse weakly
incomparable families. -/
theorem weakly_incomparable_overlap : WeaklyIncomparableOverlap := by
  intro m totalDim hm
  obtain ⟨C, c, hC, hc, h⟩ := Proof.Estimates.weakly_incomparable_overlap
  refine ⟨c m totalDim, C m totalDim, hc m totalDim, hC m totalDim, ?_⟩
  intro d hd hdim D G hG hweak eta heta heta1 hs hv
  obtain ⟨hfinite, hmoment, hexp⟩ := h m d hm hd (fun i => (D i).toProof) G hG
    ((weaklyIncomparable_iff_proof G).mp hweak) eta heta heta1
    ((sparse_iff_proof eta G).mp hs) hv
  have hfinite' : ∀ᵐ x ∂volume, overlap G x < ∞ := hfinite
  constructor
  · intro q hq
    rw [eLpNorm_eq_toReal _ hfinite']
    simpa only [hdim, overlap_eq_proof, shadow_eq_proof] using hmoment q hq
  · rw [lintegral_exp_mul_rpow_eq (shadow G) hfinite' (hc m totalDim).le
      heta.le (by positivity)]
    simpa only [hdim, overlap_eq_proof, shadow_eq_proof] using hexp

/-- The continuous Zygmund endpoint. -/
theorem continuous_endpoint : ContinuousEndpoint := by
  intro n totalDim hn
  obtain ⟨C, hC, h⟩ := Proof.Estimates.continuous_endpoint n totalDim hn
  refine ⟨C, hC, ?_⟩
  intro d hd hdim phi hphi f hf lam hlam
  rw [maximal_eq_proof]
  simpa only [continuousRectangles_eq_proof, show n + 1 - 2 = n - 1 by omega] using
    h d hd hdim phi hphi f hf lam hlam

/-- The rounded dyadic endpoint in each prescribed shifted grid. -/
theorem rounded_endpoint : RoundedEndpoint := by
  intro n totalDim hn
  obtain ⟨C, hC, h⟩ := Proof.Estimates.rounded_endpoint n totalDim hn
  refine ⟨C, hC, ?_⟩
  intro d hd hdim phi hphi tau f hf lam hlam
  rw [maximalIco_eq_proof]
  simpa only [roundedRectangles_eq_proof, show n + 1 - 2 = n - 1 by omega] using
    h d hd hdim phi hphi tau f hf lam hlam

/-- Exponential overlap for sparse Φ-Zygmund families. -/
theorem phi_sparse_overlap : PhiSparseOverlap := by
  intro n totalDim hn eta heta heta1
  obtain ⟨c, C, hc, hC, h⟩ :=
    Proof.Estimates.phi_sparse_overlap n totalDim hn eta heta heta1
  refine ⟨c, C, hc, hC, ?_⟩
  intro d hd hdim D Phi hPhi G hG hs hv
  obtain ⟨hfinite, hexp⟩ := h d hd hdim (fun i => (D i).toProof) Phi hPhi G hG
    ((sparse_iff_proof eta G).mp hs) hv
  have hfinite' : ∀ᵐ x ∂volume, overlap G x < ∞ := hfinite
  calc
    (∫⁻ x in shadow G, exp (ENNReal.ofReal c * overlap G x ^ (1 / (n : ℝ))) ∂volume) =
        ∫⁻ x in shadow G, ENNReal.ofReal
          (Real.exp (c * Real.rpow (overlap G x).toReal (1 / (n : ℝ)))) ∂volume := by
      simpa only [ENNReal.ofReal_one, one_mul] using
        lintegral_exp_mul_rpow_eq (shadow G) hfinite' hc.le (a := 1) zero_le_one
          (show 0 ≤ 1 / (n : ℝ) by positivity)
    _ ≤ ENNReal.ofReal C * volume (shadow G) := hexp

/-- Sharpness for the classical dyadic Zygmund family. -/
theorem phi_sparse_sharpness : PhiSparseSharpness := by
  intro n hn d hd D eta heta heta1
  obtain ⟨G, hG, hlim⟩ := Proof.Estimates.phi_sparse_sharpness n hn d hd
    (fun i => (D i).toProof) eta heta heta1
  refine ⟨G, ?_, ?_⟩
  · intro N hN
    exact hG N hN
  intro c beta hc hbeta
  have h := hlim c beta hc hbeta
  change Tendsto (fun N : ℕ =>
    ∫ x in shadow (G N : Set (Rectangle d)),
      Real.exp (c * Real.rpow (overlap (G N : Set (Rectangle d)) x).toReal beta)
        ∂volume) atTop atTop at h
  simpa only [overlap_toReal_finset] using h

end ReyZygmund.MathlibOnly
