import ReyZygmund.Overlap.FiniteMoments

/-! The finite overlap estimate in the extended-integral form used for limits. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Overlap

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

theorem finite_weaker_sparse_overlap_lintegral
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : ↑G ⊆ gridRectangles D)
    (hweak : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i)
    (eta : ℝ) (heta : 0 < eta)
    (E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ))
    (hEmeas : ∀ R ∈ G, MeasurableSet (E R))
    (hEsub : ∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)))
    (hEdis : Set.Pairwise (G : Set _) (fun R S => Disjoint (E R) (E S)))
    (hEmass : ∀ R ∈ G, ENNReal.ofReal eta *
      volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤ volume (E R))
    (q : ℝ) (hq : 2 ≤ q) :
    (∫⁻ x, (ENNReal.ofReal (finiteOverlap G x)) ^ q) ≤
      (ENNReal.ofReal ((maximalDimensionConstant d + 3) * eta⁻¹ * q ^ (m - 1))) ^ q *
        volume (finiteShadow G) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hJ : 0 ≤ ∫ x, Real.rpow (finiteOverlap G x) q :=
    integral_nonneg (fun x => Real.rpow_nonneg (finiteOverlap_nonneg G x) q)
  have hA : 0 ≤ volume.real (finiteShadow G) := measureReal_nonneg
  have hK : 0 ≤ maximalDimensionConstant d := by
    unfold maximalDimensionConstant
    exact sq_nonneg _
  have hC : 0 ≤ (maximalDimensionConstant d + 3) * eta⁻¹ * q ^ (m - 1) :=
    mul_nonneg (mul_nonneg (by linarith) (inv_nonneg.mpr heta.le)) (pow_nonneg hq0.le _)
  have h := finite_weaker_sparse_overlap_integral hm hd D G hG hweak eta heta E
    hEmeas hEsub hEdis hEmass q hq
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hJ _) h hq0.le
  simp only [Real.rpow_eq_pow, one_div] at hh hJ
  rw [Real.rpow_inv_rpow hJ hq0.ne',
    Real.mul_rpow hC (Real.rpow_nonneg hA _), Real.rpow_inv_rpow hA hq0.ne'] at hh
  have hE : (∫⁻ x, (ENNReal.ofReal (finiteOverlap G x)) ^ q) =
      ENNReal.ofReal (∫ x, Real.rpow (finiteOverlap G x) q) := by
    simp_rw [ENNReal.ofReal_rpow_of_nonneg (finiteOverlap_nonneg G _) hq0.le]
    exact (ofReal_integral_eq_lintegral_ofReal (integrable_rpow_finiteOverlap G q hq0)
      (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (finiteOverlap_nonneg G x) q))).symm
  rw [hE, ENNReal.ofReal_rpow_of_nonneg hC hq0.le,
    ← ofReal_measureReal (volume_finiteShadow_lt_top G).ne,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hC q)]
  simpa only [Real.rpow_eq_pow] using ENNReal.ofReal_le_ofReal hh

end ReyZygmund.Overlap
