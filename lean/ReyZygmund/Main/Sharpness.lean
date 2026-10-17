import ReyZygmund.Main.PhiSparse
import ReyZygmund.Sharpness.FlatConstruction
import ReyZygmund.Sharpness.ExponentialLower
import ReyZygmund.Sharpness.Growth

/-! # Sharpness of the sparse Zygmund overlap exponent

For each sparsity parameter, we construct one sequence of finite families whose
exponential integrals diverge for every positive coefficient and every power above
the stated threshold. The conclusion is expressed in Euclidean coordinates.
-/

open BoxIntegral MeasureTheory Filter
open scoped BigOperators Classical ENNReal Topology

namespace ReyZygmund.Main

open MathlibOnly.Proof.Estimates

open Geometry Overlap Sharpness

/-- Sharpness for the classical dyadic Zygmund family in the given grids:
the finite exponential integrals tend to infinity. -/
theorem phi_sparse_sharpness_theorem :
    ∀ (n : ℕ), 2 ≤ n →
    ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) →
      ∀ (D : ∀ i, ReyZygmund.MathlibOnly.CubeGrid (d i))
        (eta : ℝ), 0 < eta → eta < 1 →
        ∃ G : ℕ → Finset (∀ i, Box (Fin (d i))),
          (∀ N : ℕ, 2 ≤ N →
            (G N : Set (∀ i, Box (Fin (d i)))) ⊆
                ReyZygmund.MathlibOnly.dyadicZygmundRectangles D (fun k : Fin n → ℤ => ∑ i, k i) ∧
              (∀ R ∈ G N, ∀ S ∈ G N, ReyZygmund.MathlibOnly.rectangle R ⊆ ReyZygmund.MathlibOnly.rectangle S → R = S) ∧
              ReyZygmund.MathlibOnly.Sparse eta (G N : Set (∀ i, Box (Fin (d i)))) ∧
              volume (ReyZygmund.MathlibOnly.shadow (G N : Set (∀ i, Box (Fin (d i))))) = 1) ∧
          ∀ (c beta : ℝ), 0 < c → 1 / (n : ℝ) < beta →
            Tendsto (fun N : ℕ =>
              ∫⁻ x in ReyZygmund.MathlibOnly.shadow (G N : Set (∀ i, Box (Fin (d i)))),
                ENNReal.ofReal (Real.exp (c * Real.rpow
                  (ReyZygmund.MathlibOnly.overlap (G N : Set (∀ i, Box (Fin (d i)))) x).toReal beta)) - 1
                    ∂volume) atTop (𝓝 ∞) := by
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
    · simpa only [Geometry.rectangle_eq_flatProductBox] using hinc ⟨N, hN⟩
    · refine ⟨E ⟨N, hN⟩, ?_, hdis ⟨N, hN⟩⟩
      intro R hR
      refine ⟨(hE ⟨N, hN⟩ R hR).1.nullMeasurableSet, ?_, ?_⟩
      · change E ⟨N, hN⟩ R ⊆ ReyZygmund.MathlibOnly.rectangle R
        rw [Geometry.rectangle_eq_flatProductBox]
        exact (hE ⟨N, hN⟩ R hR).2.1
      · rw [Geometry.rectangle_eq_flatProductBox]
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
    · rw [shadow_eq, shadow_finset]
      exact hshadow ⟨N, hN⟩
  · intro c beta hc hbeta
    have hbeta0 : 0 < beta := lt_trans (one_div_pos.mpr (by positivity)) hbeta
    simp only [shadow_eq, overlap_eq]
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
