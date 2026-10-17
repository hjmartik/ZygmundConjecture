import ReyZygmund.MathlibOnly.Statements
import ReyZygmund.MathlibOnly.SupportingStatements
import ReyZygmund.MathlibOnly.Representation
import ReyZygmund.MathlibOnly.Proof.EstimateSolutions
import ReyZygmund.MathlibOnly.Proof.SquareSolutions
import ReyZygmund.MathlibOnly.Proof.MaximalSquareSolution
import ReyZygmund.MathlibOnly.Proof.ProductSquareSolution
import ReyZygmund.MathlibOnly.Proof.ProjectionAverageSolutions
import ReyZygmund.MathlibOnly.Proof.ProjectionDifferencesSolution
import ReyZygmund.MathlibOnly.Proof.AveragingFamilySolutions
import ReyZygmund.MathlibOnly.Proof.ProjectedSquareSolutions
import ReyZygmund.MathlibOnly.Proof.CoveringSolution
import ReyZygmund.MathlibOnly.Proof.SelectionSolution
import ReyZygmund.MathlibOnly.Proof.SliceSolutions
import ReyZygmund.MathlibOnly.Proof.DyadicEndpointSolution

/-!
# Proofs of the independent statements

The analytic estimates use the specification's rectangle families and operators.
The identities in `Representation.lean` express the real-valued estimates as
extended norms and exponential integrals.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Classical Topology

namespace ReyZygmund.MathlibOnly

/-- The weakly incomparable maximal estimate. -/
theorem weakly_incomparable_maximal_estimate : WeaklyIncomparableMaximalEstimate := by
  intro m totalDim hm
  obtain ⟨C, hC, h⟩ := Proof.Estimates.weakly_incomparable_maximal
  refine ⟨C m totalDim, hC m totalDim, ?_⟩
  intro d hd hdim D G hG hweak p hp hp2 f hf
  obtain ⟨hfinite, hbound⟩ := h m d hm hd D G hG
    hweak p hp hp2 f hf
  rw [eLpNorm_eq_toReal _ hfinite]
  simpa only [hdim] using hbound

/-- The moment and exponential overlap bounds for sparse weakly
incomparable families. -/
theorem weakly_incomparable_rey_conjecture : WeaklyIncomparableReyConjecture := by
  intro m totalDim hm
  obtain ⟨C, c, hC, hc, h⟩ := Proof.Estimates.weakly_incomparable_overlap
  refine ⟨c m totalDim, C m totalDim, hc m totalDim, hC m totalDim, ?_⟩
  intro d hd hdim D G hG hweak eta heta heta1 hs hv
  obtain ⟨hfinite, hmoment, hexp⟩ := h m d hm hd D G hG
    hweak eta heta heta1 hs hv
  constructor
  · intro q hq
    rw [eLpNorm_eq_toReal _ hfinite]
    simpa only [hdim] using hmoment q hq
  · rw [lintegral_exp_mul_rpow_eq (shadow G) hfinite (hc m totalDim).le
      heta.le (by positivity)]
    simpa only [hdim] using hexp

/-- The continuous Zygmund endpoint. -/
theorem zygmund_conjecture : ZygmundConjecture := by
  intro n totalDim hn
  obtain ⟨C, hC, h⟩ := Proof.Estimates.continuous_endpoint n totalDim hn
  refine ⟨C, hC, ?_⟩
  intro d hd hdim phi hphi f hf lam hlam
  simpa only [show n + 1 - 2 = n - 1 by omega] using
    h d hd hdim phi hphi f hf lam hlam

/-- The rounded dyadic endpoint in each prescribed shifted grid. -/
theorem rounded_dyadic_endpoint_estimate : RoundedDyadicEndpointEstimate := by
  intro n totalDim hn
  obtain ⟨C, hC, h⟩ := Proof.Estimates.rounded_endpoint n totalDim hn
  refine ⟨C, hC, ?_⟩
  intro d hd hdim phi hphi tau f hf lam hlam
  simpa only [show n + 1 - 2 = n - 1 by omega] using
    h d hd hdim phi hphi tau f hf lam hlam

/-- Exponential overlap for sparse Φ-Zygmund families. -/
theorem sparse_phi_zygmund_overlap_estimate : SparsePhiZygmundOverlapEstimate := by
  intro n totalDim hn eta heta heta1
  obtain ⟨c, C, hc, hC, h⟩ :=
    Proof.Estimates.phi_sparse_overlap n totalDim hn eta heta heta1
  refine ⟨c, C, hc, hC, ?_⟩
  intro d hd hdim D Phi hPhi G hG hs hv
  obtain ⟨hfinite, hexp⟩ := h d hd hdim D Phi hPhi G hG hs hv
  calc
    (∫⁻ x in shadow G, exp (ENNReal.ofReal c * overlap G x ^ (1 / (n : ℝ))) ∂volume) =
        ∫⁻ x in shadow G, ENNReal.ofReal
          (Real.exp (c * Real.rpow (overlap G x).toReal (1 / (n : ℝ)))) ∂volume := by
      simpa only [ENNReal.ofReal_one, one_mul] using
        lintegral_exp_mul_rpow_eq (shadow G) hfinite hc.le (a := 1) zero_le_one
          (show 0 ≤ 1 / (n : ℝ) by positivity)
    _ ≤ ENNReal.ofReal C * volume (shadow G) := hexp

/-- Sharpness for the classical dyadic Zygmund family. -/
theorem classical_dyadic_zygmund_sharpness : ClassicalDyadicZygmundSharpness := by
  intro n hn d hd D eta heta heta1
  obtain ⟨G, hG, hlim⟩ := Proof.Estimates.phi_sparse_sharpness n hn d hd
    D eta heta heta1
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
