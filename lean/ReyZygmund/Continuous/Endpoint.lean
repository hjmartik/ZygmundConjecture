import ReyZygmund.Continuous.RoundedEndpoint
import ReyZygmund.Continuous.Cover
import ReyZygmund.Continuous.Measurability

/-! # Continuous endpoint transfer

The finite prescribed-shift cover transfers the proved rounded estimate to
the all-position operator. The dilation of the Orlicz expression is
bounded explicitly; every constant is chosen before the side function.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Continuous

open Geometry

/-- The elementary logarithmic dilation used in the continuous endpoint. -/
theorem log_dilation_le {A u : ℝ} (hA : 1 ≤ A) (hu : 0 ≤ u) :
    Real.log (Real.exp 1 + A * u) ≤
      (1 + Real.log A) * Real.log (Real.exp 1 + u) := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have he : 0 < Real.exp (1 : ℝ) := Real.exp_pos _
  have hL : 1 ≤ Real.log (Real.exp 1 + u) := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp _).symm
      _ ≤ Real.log (Real.exp 1 + u) := Real.log_le_log he (by linarith)
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  calc
    Real.log (Real.exp 1 + A * u) ≤ Real.log (A * (Real.exp 1 + u)) :=
      Real.log_le_log (by positivity) (by nlinarith)
    _ = Real.log A + Real.log (Real.exp 1 + u) :=
      Real.log_mul hApos.ne' (by positivity)
    _ ≤ (1 + Real.log A) * Real.log (Real.exp 1 + u) := by
      nlinarith [mul_le_mul_of_nonneg_left hL hlogA]

theorem orlicz_dilation_le (q : ℕ) {A u : ℝ} (hA : 1 ≤ A) (hu : 0 ≤ u) :
    (A * u) * (Real.log (Real.exp 1 + A * u)) ^ q ≤
      (A * (1 + Real.log A) ^ q) *
        (u * (Real.log (Real.exp 1 + u)) ^ q) := by
  have hlog : 0 ≤ Real.log (Real.exp 1 + A * u) := by
    apply Real.log_nonneg
    have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
    nlinarith [mul_nonneg (le_trans zero_le_one hA) hu]
  have h := pow_le_pow_left₀ hlog (log_dilation_le hA hu) q
  have hh := mul_le_mul_of_nonneg_left h (mul_nonneg (le_trans zero_le_one hA) hu)
  simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hh

theorem prescribed_shift_count {m : ℕ} (d : Fin m → ℕ) :
    Fintype.card (∀ i, Fin (d i) → Fin 3) = 3 ^ (∑ i, d i) := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fun, Fintype.card_fin]
  exact Finset.prod_pow_eq_pow_sum Finset.univ d (3 : ℕ)

theorem continuous_levelset_subset_rounded {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf : LocallyIntegrable f volume)
    (lam : ℝ) (hlam : 0 < lam) :
    {x | ENNReal.ofReal lam < euclideanFamilyMaximal (continuousPhiRectangles d phi) f x} ⊆
      ⋃ tau : (∀ i, Fin (d i) → Fin 3),
        {x | ENNReal.ofReal (lam / (8 : ℝ) ^ (∑ i, d i)) <
          euclideanFamilyMaximal
            (roundedGridRectangles (fun i => shiftedDyadicGrid (d i) (tau i)) phi) f x} := by
  intro x hx
  by_contra hnot
  have hle : (⨆ tau : (∀ i, Fin (d i) → Fin 3),
      euclideanFamilyMaximal
        (roundedGridRectangles (fun i => shiftedDyadicGrid (d i) (tau i)) phi) f x) ≤
        ENNReal.ofReal (lam / (8 : ℝ) ^ (∑ i, d i)) := by
    apply iSup_le
    intro tau
    apply le_of_not_gt
    intro ht
    exact hnot (Set.mem_iUnion.mpr ⟨tau, ht⟩)
  have hdom := (continuous_maximal_le_rounded phi f hf x).trans
    (mul_le_mul' le_rfl hle)
  have heq : ENNReal.ofReal ((8 : ℝ) ^ (∑ i, d i)) *
      ENNReal.ofReal (lam / (8 : ℝ) ^ (∑ i, d i)) = ENNReal.ofReal lam := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [heq] at hdom
  exact (not_lt_of_ge hdom) hx

/-- The continuous endpoint, uniform in the positive monotone side
function and all positive block dimensions of the prescribed total. -/
theorem continuous_endpoint_theorem :
    ∀ (n totalDim : ℕ), 2 ≤ n →
    ∃ C : ℝ, 0 < C ∧
    ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
    ∀ (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)), Monotone phi →
    ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
    ∀ (lam : ℝ), 0 < lam →
      volume {x | ENNReal.ofReal lam <
        euclideanFamilyMaximal (continuousPhiRectangles d phi) f x} ≤
      ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
        (|f x| / lam * (Real.log (Real.exp 1 + |f x| / lam)) ^ ((n + 1) - 2)) := by
  intro n totalDim hn
  obtain ⟨C0, hC0, hrounded⟩ := rounded_grid_endpoint_theorem n totalDim hn
  let A : ℝ := 8 ^ totalDim
  let B : ℝ := A * (1 + Real.log A) ^ (n - 1)
  have hA : 1 ≤ A := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 8)
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hB : 0 < B := mul_pos hApos (pow_pos (by linarith [Real.log_nonneg hA]) _)
  refine ⟨(3 : ℝ) ^ totalDim * C0 * B, by positivity, ?_⟩
  intro d hd hsum phi hphi f hf lam hlam
  let F : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal
    (|f x| / lam * (Real.log (Real.exp 1 + |f x| / lam)) ^ (n - 1))
  have hscaled : (∫⁻ x, ENNReal.ofReal
      (|f x| / (lam / A) * (Real.log (Real.exp 1 + |f x| / (lam / A))) ^ (n - 1))) ≤
        ENNReal.ofReal B * F := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal B * ENNReal.ofReal
          (|f x| / lam * (Real.log (Real.exp 1 + |f x| / lam)) ^ (n - 1)) := by
        apply lintegral_mono
        intro x
        dsimp only
        rw [← ENNReal.ofReal_mul hB.le]
        apply ENNReal.ofReal_le_ofReal
        have hratio : |f x| / (lam / A) = A * (|f x| / lam) := by
          field_simp
        rw [hratio]
        exact orlicz_dilation_le (n - 1) hA (div_nonneg (abs_nonneg _) hlam.le)
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hbound (tau : ∀ i, Fin (d i) → Fin 3) :
      volume {x | ENNReal.ofReal (lam / A) < euclideanFamilyMaximal
        (roundedGridRectangles (fun i => shiftedDyadicGrid (d i) (tau i)) phi) f x} ≤
        (ENNReal.ofReal C0 * ENNReal.ofReal B) * F := by
    have h := hrounded d hd hsum (fun i => shiftedDyadicGrid (d i) (tau i))
      phi hphi f hf (lam / A) (div_pos hlam hApos)
    exact h.trans (by simpa only [mul_assoc] using mul_le_mul' le_rfl hscaled)
  have hsub := continuous_levelset_subset_rounded phi f hf lam hlam
  have hpow : (8 : ℝ) ^ (∑ i, d i) = A := by rw [hsum]
  rw [hpow] at hsub
  have hmain : volume {x | ENNReal.ofReal lam <
      euclideanFamilyMaximal (continuousPhiRectangles d phi) f x} ≤
      ((Fintype.card (∀ i, Fin (d i) → Fin 3) : ℝ≥0∞) *
        (ENNReal.ofReal C0 * ENNReal.ofReal B)) * F := by
    calc
      _ ≤ volume (⋃ tau : (∀ i, Fin (d i) → Fin 3),
          {x | ENNReal.ofReal (lam / A) < euclideanFamilyMaximal
            (roundedGridRectangles (fun i => shiftedDyadicGrid (d i) (tau i)) phi) f x}) :=
        measure_mono hsub
      _ ≤ ∑' tau : (∀ i, Fin (d i) → Fin 3),
          volume {x | ENNReal.ofReal (lam / A) < euclideanFamilyMaximal
            (roundedGridRectangles (fun i => shiftedDyadicGrid (d i) (tau i)) phi) f x} :=
        measure_iUnion_le _
      _ ≤ ∑' _tau : (∀ i, Fin (d i) → Fin 3),
          (ENNReal.ofReal C0 * ENNReal.ofReal B) * F := ENNReal.tsum_le_tsum hbound
      _ = _ := by simp only [tsum_fintype, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_assoc]
  have hcard : (Fintype.card (∀ i, Fin (d i) → Fin 3) : ℝ≥0∞) =
      ENNReal.ofReal ((3 : ℝ) ^ totalDim) := by
    rw [prescribed_shift_count, hsum]
    simp
  rw [hcard] at hmain
  simpa only [show n + 1 - 2 = n - 1 by omega, F,
    ENNReal.ofReal_mul (show 0 ≤ (3 : ℝ) ^ totalDim * C0 by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (3 : ℝ) ^ totalDim by positivity),
    ENNReal.ofReal_mul hC0.le, mul_assoc] using hmain

end ReyZygmund.Continuous
