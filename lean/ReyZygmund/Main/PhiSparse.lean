import ReyZygmund.Overlap.Phi
import Verification.Challenges.PhiSparse

/-! # Sparse overlap for monotone Zygmund scale relations

The countable endpoint argument gives exponential integrability of the sparse
overlap. The rectangles, shadow and overlap agree with their independently stated
definitions in Euclidean coordinates. These identities are also used for
sharpness.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Main

open Geometry Overlap ReyZygmund.Continuous

theorem phiSparse_rectangle_eq {m : ℕ} {d : Fin m → ℕ}
    (R : ∀ i, Box (Fin (d i))) :
    ReyZygmundVerification.Challenges.rectangle R =
      (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) := by
  ext x
  obtain ⟨y, rfl⟩ := (flattenCoordinates d).surjective x
  apply Iff.trans _ (mem_flatProductBox R y).symm
  simp only [ReyZygmundVerification.Challenges.rectangle, Set.mem_ofPred_eq,
    mem_productBox, flattenCoordinates_apply]
  rfl

theorem phiSparse_shadow_eq {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i)))) :
    ReyZygmundVerification.Challenges.shadow G = shadow G := by
  ext x
  simp only [ReyZygmundVerification.Challenges.shadow, shadow,
    phiSparse_rectangle_eq, Set.mem_iUnion, Subtype.exists]

theorem phiSparse_overlap_eq {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i)))) :
    ReyZygmundVerification.Challenges.overlap G = overlap G := by
  funext x
  simp only [ReyZygmundVerification.Challenges.overlap, overlap, phiSparse_rectangle_eq]

theorem phiSparse_grid_eq {n : ℕ} {d : Fin (n + 1) → ℕ}
    (D : ∀ i, DyadicGrid (d i)) (Phi : (Fin n → ℤ) → ℤ) :
    ReyZygmundVerification.Challenges.phiGridRectangles D Phi =
      dyadicPhiRectangles D Phi := rfl

/-- The full source sparse-Phi theorem: arbitrary supplied dyadic grids and
positive block dimensions, countable sparse families, and uniform constants
chosen before the side relation and the family. -/
theorem phi_sparse_overlap_theorem :
    ReyZygmundVerification.Challenges.phiSparseOverlapStatement := by
  intro n totalDim hn eta heta _heta1
  obtain ⟨c, C, hc, hC, hbound⟩ := phi_sparse_overlap_exponential n totalDim hn eta heta
  refine ⟨c, C, hc, hC, ?_⟩
  intro d hd hdim D Phi hPhi G hG hsparse hshadow
  obtain ⟨E, hEm, hEs, hEd, hEv⟩ := hsparse
  simp only [phiSparse_rectangle_eq] at hEs hEv
  rw [phiSparse_grid_eq] at hG
  rw [phiSparse_shadow_eq] at hshadow
  rw [phiSparse_overlap_eq, phiSparse_shadow_eq]
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
