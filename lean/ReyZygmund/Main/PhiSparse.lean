import ReyZygmund.Overlap.Phi
import ReyZygmund.MathlibOnly.Proof.OverlapBridge

/-! # Sparse overlap for monotone Zygmund scale relations

The countable endpoint argument gives exponential integrability of the sparse
overlap, expressed here in Euclidean coordinates.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Main

open MathlibOnly.Proof.Estimates

open Geometry Overlap ReyZygmund.Continuous

/-- Sparse overlap for a monotone Zygmund scale relation, with constants
depending on the number of factors, total dimension and sparsity parameter. -/
theorem phi_sparse_overlap_theorem :
    ∀ (n totalDim : ℕ), 2 ≤ n →
    ∀ (eta : ℝ), 0 < eta → eta ≤ 1 →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
          ∀ (D : ∀ i, ReyZygmund.MathlibOnly.CubeGrid (d i))
            (Phi : (Fin n → ℤ) → ℤ), Monotone Phi →
            ∀ (G : Set (∀ i, Box (Fin (d i)))),
              G ⊆ ReyZygmund.MathlibOnly.dyadicZygmundRectangles D Phi → ReyZygmund.MathlibOnly.Sparse eta G → volume (ReyZygmund.MathlibOnly.shadow G) < ∞ →
                (∀ᵐ x ∂volume, ReyZygmund.MathlibOnly.overlap G x < ∞) ∧
                  (∫⁻ x in ReyZygmund.MathlibOnly.shadow G, ENNReal.ofReal
                    (Real.exp (c * Real.rpow (ReyZygmund.MathlibOnly.overlap G x).toReal (1 / (n : ℝ)))) - 1
                      ∂volume) ≤ ENNReal.ofReal C * volume (ReyZygmund.MathlibOnly.shadow G) := by
  intro n totalDim hn eta heta _heta1
  obtain ⟨c, C, hc, hC, hbound⟩ := phi_sparse_overlap_exponential n totalDim hn eta heta
  refine ⟨c, C, hc, hC, ?_⟩
  intro d hd hdim D Phi hPhi G hG hsparse hshadow
  obtain ⟨E, hE, hEd⟩ := hsparse
  have hEm := fun R hR => (hE R hR).1
  have hEs : ∀ R ∈ G, E R ⊆ ReyZygmund.MathlibOnly.rectangle R :=
    fun R hR => (hE R hR).2.1
  have hEv : ∀ R ∈ G,
      ENNReal.ofReal eta * volume (ReyZygmund.MathlibOnly.rectangle R) ≤
        volume (E R) := fun R hR => (hE R hR).2.2
  simp only [Geometry.rectangle_eq_flatProductBox] at hEs hEv
  rw [shadow_eq] at hshadow
  rw [overlap_eq, shadow_eq]
  have h := hbound d hd hdim D Phi hPhi G hG E hEm hEs hEd hEv hshadow
  refine ⟨h.1, ?_⟩
  calc
    _ = ∫⁻ x in shadow G, ENNReal.ofReal
        (Real.exp (c * (overlap G x).toReal ^ (1 / (n : ℝ))) - 1) := by
      apply lintegral_congr
      intro x
      rw [ENNReal.ofReal_sub _ (by norm_num : (0 : ℝ) ≤ 1), ENNReal.ofReal_one]
      simp only [Real.rpow_eq_pow]
    _ ≤ _ := h.2

end ReyZygmund.Main
