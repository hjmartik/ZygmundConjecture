import ReyZygmund.Overlap.Exponential
import ReyZygmund.Overlap.FiniteIdentification

/-! # The finite half-sparse exponential estimate

This is the already proved overlap theorem in the finite notation
used for slices. The one-half factor is absorbed into the positive constant,
and the constant term is integrated only over the finite shadow.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Overlap

open Geometry

theorem finite_half_sparse_exponential :
    ∃ c B : ℕ → ℕ → ℝ,
      (∀ m D, 0 < c m D) ∧ (∀ m D, 0 < B m D) ∧
      ∀ (m : ℕ) (d : Fin m → ℕ), 2 ≤ m → (∀ i, 0 < d i) →
      ∀ (D : ∀ i, DyadicGrid (d i)) (G : Finset (∀ i, Box (Fin (d i)))),
      (↑G : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D →
      (∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i) →
      ∀ E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ),
      (∀ R ∈ G, MeasurableSet (E R)) →
      (∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) →
      Set.Pairwise (↑G) (fun R S => Disjoint (E R) (E S)) →
      (∀ R ∈ G, ENNReal.ofReal (1 / 2 : ℝ) *
        volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤ volume (E R)) →
      (∫⁻ x in finiteShadow G, ENNReal.ofReal
        (Real.exp (c m (∑ i, d i) *
          Real.rpow (finiteOverlap G x) (1 / ((m - 1 : ℕ) : ℝ))))) ≤
        ENNReal.ofReal (B m (∑ i, d i)) * volume (finiteShadow G) := by
  obtain ⟨c, B, hc, hB, hspec⟩ := weaker_sparse_overlap_exponential
  refine ⟨fun m D => c m D * Real.rpow (1 / 2) (1 / ((m - 1 : ℕ) : ℝ)),
    fun m D => B m D + 1, ?_, ?_, ?_⟩
  · intro m D
    exact mul_pos (hc m D) (Real.rpow_pos_of_pos (by norm_num) _)
  · intro m D
    linarith [hB m D]
  intro m d hm hd D G hG hweak E hEmeas hEsub hEdis hEmass
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hminus := hspec m d hm hd D (↑G) hG hweak (1 / 2) hhalf E
    hEmeas hEsub hEdis hEmass (by simpa only [shadow_finset] using volume_finiteShadow_lt_top G)
  simp only [shadow_finset, toReal_overlap_finset] at hminus
  let v := fun x => c m (∑ i, d i) *
    Real.rpow ((1 / 2 : ℝ) * finiteOverlap G x) (1 / ((m - 1 : ℕ) : ℝ))
  have hv : Measurable v := by
    dsimp [v]
    simpa only [Real.rpow_eq_pow] using
      (((measurable_finiteOverlap G).const_mul (1 / 2)).pow_const
        (1 / ((m - 1 : ℕ) : ℝ))).const_mul (c m (∑ i, d i))
  have hv0 (x) : 0 ≤ v x :=
    mul_nonneg (hc _ _).le (Real.rpow_nonneg
      (mul_nonneg hhalf.le (finiteOverlap_nonneg G x)) _)
  have hnonneg (x) : 0 ≤ Real.exp (v x) - 1 := by
    linarith [Real.one_le_exp_iff.mpr (hv0 x)]
  have hpoint (x) : ENNReal.ofReal (Real.exp (v x)) =
      ENNReal.ofReal (Real.exp (v x) - 1) + 1 := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (hnonneg x) zero_le_one]
    congr 1
    ring
  have hscaled (x) :
      (c m (∑ i, d i) * Real.rpow (1 / 2) (1 / ((m - 1 : ℕ) : ℝ))) *
        Real.rpow (finiteOverlap G x) (1 / ((m - 1 : ℕ) : ℝ)) = v x := by
    dsimp [v]
    rw [Real.mul_rpow hhalf.le (finiteOverlap_nonneg G x), mul_assoc]
  simp only [hscaled]
  calc
    (∫⁻ x in finiteShadow G, ENNReal.ofReal (Real.exp (v x))) =
        (∫⁻ x in finiteShadow G, ENNReal.ofReal (Real.exp (v x) - 1)) +
          volume (finiteShadow G) := by
      simp_rw [hpoint]
      rw [lintegral_add_left ((hv.exp.sub_const 1).ennreal_ofReal)]
      simp
    _ ≤ ENNReal.ofReal (B m (∑ i, d i)) * volume (finiteShadow G) +
        volume (finiteShadow G) := add_le_add hminus le_rfl
    _ = ENNReal.ofReal (B m (∑ i, d i) + 1) * volume (finiteShadow G) := by
      rw [ENNReal.ofReal_add (hB _ _).le zero_le_one, ENNReal.ofReal_one, add_mul, one_mul]

end ReyZygmund.Overlap
