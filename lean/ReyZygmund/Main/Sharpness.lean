import ReyZygmund.Main.PhiSparse
import ReyZygmund.Sharpness.FlatConstruction
import ReyZygmund.Sharpness.ExponentialLower
import ReyZygmund.Sharpness.Growth

/-! # Sharpness of the sparse Zygmund overlap exponent

For each sparse parameter, we construct one sequence of finite families whose
exponential integrals diverge for every positive coefficient and every power above
the stated threshold. The conclusion is expressed in Euclidean coordinates.
-/

open BoxIntegral MeasureTheory Filter
open scoped BigOperators Classical ENNReal Topology

namespace ReyZygmund.Main

open Geometry Overlap Sharpness

/-- Full sharpness for the sum side relation in arbitrary supplied grids.
The individual integrals are finite, and their values tend to infinity. -/
theorem phi_sparse_sharpness_theorem :
    ReyZygmundVerification.Challenges.phiSparseSharpnessStatement := by
  intro n hn
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, n = r + 2 := ⟨n - 2, by omega⟩
  intro d hd D eta heta heta1
  obtain ⟨s, hs, hfrac⟩ := exists_retention_scale (r + 2) (by omega) eta heta heta1
  let delta : ℝ := (2 : ℝ) ^ (-(s : ℤ))
  have hdelta : 0 < delta := zpow_pos (by norm_num) _
  have hdelta1 : delta < 1 := zpow_lt_one_of_neg₀ (by norm_num) (by omega)
  choose G E L hgrid hinc hshadow hE hdis hLm hLs hlevel hmass using
    (fun N : {N : ℕ // 2 ≤ N} =>
      exists_sharp_flat_construction r N.1 s N.2 hs d hd D)
  let family (N : ℕ) : Finset (∀ i, Box (Fin (d i))) :=
    if h : 2 ≤ N then G ⟨N, h⟩ else ∅
  refine ⟨family, ?_, ?_⟩
  · intro N hN
    simp only [family, dite_eq_left hN]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hgrid ⟨N, hN⟩
    · simpa only [phiSparse_rectangle_eq] using hinc ⟨N, hN⟩
    · refine ⟨E ⟨N, hN⟩, ?_, ?_, hdis ⟨N, hN⟩, ?_⟩
      · exact fun R hR => (hE ⟨N, hN⟩ R hR).1
      · intro R hR
        rw [phiSparse_rectangle_eq]
        exact (hE ⟨N, hN⟩ R hR).2.1
      · intro R hR
        rw [phiSparse_rectangle_eq]
        have hvR := (flatProductBox R).measure_coe_lt_top volume
        have hvE : volume (E ⟨N, hN⟩ R) < ⊤ :=
          (measure_mono (hE ⟨N, hN⟩ R hR).2.1).trans_lt hvR
        have hreal : eta * volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤
            volume.real (E ⟨N, hN⟩ R) := by
          rw [(hE ⟨N, hN⟩ R hR).2.2]
          exact mul_le_mul_of_nonneg_right hfrac ENNReal.toReal_nonneg
        calc
          ENNReal.ofReal eta * volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) =
              ENNReal.ofReal (eta * volume.real
                (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) := by
            rw [ENNReal.ofReal_mul heta.le, measureReal_def, ENNReal.ofReal_toReal hvR.ne]
          _ ≤ ENNReal.ofReal (volume.real (E ⟨N, hN⟩ R)) := ENNReal.ofReal_le_ofReal hreal
          _ = volume (E ⟨N, hN⟩ R) := ENNReal.ofReal_toReal hvE.ne
    · rw [phiSparse_shadow_eq, shadow_finset]
      exact hshadow ⟨N, hN⟩
  · intro c beta hc hbeta
    have hbeta0 : 0 < beta := lt_trans (one_div_pos.mpr (by positivity)) hbeta
    simp only [phiSparse_shadow_eq, phiSparse_overlap_eq]
    apply (tendsto_finite_overlap_exponential_iff family c beta hc hbeta0).mpr
    have hdiv := tendsto_retained_exp_lower_bound (r + 2) (by omega)
      delta c beta hdelta hdelta1 hc hbeta
    apply tendsto_atTop_mono' atTop ?_ hdiv
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have h := finite_overlap_exponential_lower (G ⟨N, hN⟩) (L ⟨N, hN⟩)
      (hLm ⟨N, hN⟩) (hLs ⟨N, hN⟩) ((N : ℝ) ^ (r + 2)) c beta
      (hlevel ⟨N, hN⟩) hc hbeta0
    rw [hmass ⟨N, hN⟩] at h
    simpa only [family, dite_eq_left hN, delta, Real.rpow_eq_pow,
      Real.rpow_natCast_mul (Nat.cast_nonneg N)] using h

end ReyZygmund.Main
