import ReyZygmund.Overlap.Global
import ReyZygmund.Overlap.MomentsToExponential

/-! # Uniform exponential integrability from the sparse-overlap moments -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Overlap

open Geometry

/-- A constant for the overlap moments, written in terms of parameter count and
total dimension so that its dependence is explicit. -/
noncomputable def momentConstant (m D : ℕ) : ℝ :=
  (2 * (1 + ((m : ℝ) * (2 : ℝ) ^ m *
      ((2 : ℝ) ^ (6 * D + 10) + (2 : ℝ) ^ (m - 1))) *
    (1 + Real.sqrt ((m : ℝ) * (2 : ℝ) ^ (D + (m - 1)))))) ^ 2 + 3

theorem momentConstant_pos (m D : ℕ) : 0 < momentConstant m D := by
  unfold momentConstant
  positivity

theorem momentConstant_eq {m : ℕ} (d : Fin m → ℕ) :
    momentConstant m (∑ i, d i) = maximalDimensionConstant d + 3 := rfl

private theorem scaled_overlap_moment
    {m : ℕ} {d : Fin m → ℕ}
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (hweak : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i)
    (eta : ℝ) (heta : 0 < eta)
    (E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ))
    (hEmeas : ∀ R ∈ G, MeasurableSet (E R))
    (hEsub : ∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)))
    (hEdis : Set.Pairwise G (fun R S => Disjoint (E R) (E S)))
    (hEmass : ∀ R ∈ G, ENNReal.ofReal eta *
      volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤ volume (E R))
    (q : ℝ) (hq : 2 ≤ q) :
    (∫⁻ x in shadow G, (ENNReal.ofReal (eta * (overlap G x).toReal)) ^ q) ≤
      (ENNReal.ofReal (momentConstant m (∑ i, d i) * q ^ (m - 1))) ^ q *
        volume (shadow G) := by
  have hq0 : 0 ≤ q := (by norm_num : (0 : ℝ) ≤ 2).trans hq
  have hbound := weaker_sparse_overlap_lintegral hm hd D G hG hweak eta heta E
    hEmeas hEsub hEdis hEmass q hq
  have hpoint (x : Fin (∑ i, d i) → ℝ) :
      (ENNReal.ofReal (eta * (overlap G x).toReal)) ^ q ≤
        (ENNReal.ofReal eta) ^ q * (overlap G x) ^ q := by
    rw [ENNReal.ofReal_mul heta.le, ENNReal.mul_rpow_of_nonneg _ _ hq0]
    exact mul_le_mul_right (ENNReal.rpow_le_rpow ENNReal.ofReal_toReal_le hq0) _
  calc
    _ ≤ ∫⁻ x, (ENNReal.ofReal (eta * (overlap G x).toReal)) ^ q :=
      lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ ≤ ∫⁻ x, (ENNReal.ofReal eta) ^ q * (overlap G x) ^ q := lintegral_mono hpoint
    _ = (ENNReal.ofReal eta) ^ q * ∫⁻ x, (overlap G x) ^ q :=
      lintegral_const_mul' _ _ (ENNReal.rpow_lt_top_of_nonneg hq0 ENNReal.ofReal_ne_top).ne
    _ ≤ (ENNReal.ofReal eta) ^ q *
        ((ENNReal.ofReal ((maximalDimensionConstant d + 3) * eta⁻¹ * q ^ (m - 1))) ^ q *
          volume (shadow G)) := mul_le_mul_right hbound _
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ hq0,
        ← ENNReal.ofReal_mul heta.le]
      congr 2
      rw [momentConstant_eq]
      field_simp

/-- Dimension-only constants work for every sparse family satisfying the
weaker containment condition. They are chosen before the grids, family,
sparsity fraction and shadow. -/
theorem weaker_sparse_overlap_exponential :
    ∃ c B : ℕ → ℕ → ℝ,
      (∀ m D, 0 < c m D) ∧ (∀ m D, 0 < B m D) ∧
      ∀ (m : ℕ) (d : Fin m → ℕ), 2 ≤ m → (∀ i, 0 < d i) →
      ∀ (D : ∀ i, DyadicGrid (d i)) (G : Set (∀ i, Box (Fin (d i)))),
      G ⊆ gridRectangles D →
      (∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i) →
      ∀ eta : ℝ, 0 < eta →
      ∀ E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ),
      (∀ R ∈ G, MeasurableSet (E R)) →
      (∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) →
      Set.Pairwise G (fun R S => Disjoint (E R) (E S)) →
      (∀ R ∈ G, ENNReal.ofReal eta *
        volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤ volume (E R)) →
      volume (shadow G) < ∞ →
      (∫⁻ x in shadow G, ENNReal.ofReal
        (Real.exp (c m (∑ i, d i) *
          Real.rpow (eta * (overlap G x).toReal) (1 / ((m - 1 : ℕ) : ℝ))) - 1)) ≤
        ENNReal.ofReal (B m (∑ i, d i)) * volume (shadow G) := by
  choose c B hc hB hspec using fun m D =>
    moments_to_exponential.{0} (max 1 (m - 1)) (le_max_left _ _)
      (momentConstant m D) (momentConstant_pos m D)
  refine ⟨c, B, hc, hB, ?_⟩
  intro m d hm hd D G hG hweak eta heta E hEmeas hEsub hEdis hEmass hshadow
  have hcG : G.Countable := (countable_gridRectangles D).mono hG
  let μ := volume.restrict (shadow G)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hshadow.ne
  have hk : max 1 (m - 1) = m - 1 := max_eq_right (by omega)
  have hHmeas : Measurable (fun x => eta * (overlap G x).toReal) :=
    (measurable_overlap G hcG).ennreal_toReal.const_mul eta
  have h := hspec m (∑ i, d i) μ (fun x => eta * (overlap G x).toReal) hHmeas
    (fun x => mul_nonneg heta.le ENNReal.toReal_nonneg) (by
      intro q hq
      simpa only [μ, hk, Measure.restrict_apply_univ] using
        scaled_overlap_moment hm hd D G hG hweak eta heta E hEmeas hEsub hEdis hEmass q hq)
  simpa only [μ, hk, Measure.restrict_apply_univ] using h

end ReyZygmund.Overlap
