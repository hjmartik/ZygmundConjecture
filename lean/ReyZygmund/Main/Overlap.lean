import ReyZygmund.Main.Maximal
import ReyZygmund.Maximal.WeakerGlobal
import ReyZygmund.Overlap.Exponential
import ReyZygmund.MathlibOnly.Proof.OverlapBridge

/-! # Maximal and sparse overlap estimates

We use the form of weak incomparability in which containment leaves one factor
unchanged, then specialize to incomparable families.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Main

open MathlibOnly.Proof.Estimates

open Geometry Overlap

private theorem weak_containment_transfer {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i))))
    (hweak : ∀ R ∈ G, ∀ S ∈ G,
      ReyZygmund.MathlibOnly.rectangle R ⊆
        ReyZygmund.MathlibOnly.rectangle S → ∃ i, R i = S i) :
    ∀ R ∈ G, ∀ S ∈ G, productRectangle R ⊆ productRectangle S → ∃ i, R i = S i := by
  intro R hR S hS hRS
  apply hweak R hR S hS
  rw [rectangle_eq_flatProductBox, rectangle_eq_flatProductBox]
  intro x hx
  obtain ⟨y, rfl⟩ := (flattenCoordinates d).surjective x
  exact (mem_flatProductBox S y).mpr (hRS ((mem_flatProductBox R y).mp hx))

/-- The maximal estimate and sparse overlap bounds under weak incomparability,
expressed through containment that leaves one factor unchanged. -/
theorem weaker_containment_theorem :
    ∃ C c : ℕ → ℕ → ℝ,
    (∀ m D, 0 < C m D) ∧ (∀ m D, 0 < c m D) ∧
    ∀ (m : ℕ) (d : Fin m → ℕ), 2 ≤ m → (∀ i : Fin m, 0 < d i) →
      ∀ (D : ∀ i : Fin m, ReyZygmund.MathlibOnly.CubeGrid (d i))
        (G : Set (∀ i : Fin m, Box (Fin (d i)))),
        G ⊆ ReyZygmund.MathlibOnly.gridRectangles D →
        (∀ R ∈ G, ∀ S ∈ G, ReyZygmund.MathlibOnly.rectangle R ⊆ ReyZygmund.MathlibOnly.rectangle S →
          ∃ i : Fin m, R i = S i) →
        ((∀ (p : ℝ), 1 < p → p ≤ 2 →
          ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ),
            MemLp f (ENNReal.ofReal p) volume →
            (∀ᵐ x ∂volume, ReyZygmund.MathlibOnly.maximal G f x < ∞) ∧
              eLpNorm (fun x => (ReyZygmund.MathlibOnly.maximal G f x).toReal)
                  (ENNReal.ofReal p) volume ≤
                ENNReal.ofReal (C m (∑ i, d i) * (p / (p - 1)) ^ (m - 1)) *
                  eLpNorm f (ENNReal.ofReal p) volume) ∧
        (∀ (η : ℝ), 0 < η → η ≤ 1 → ReyZygmund.MathlibOnly.Sparse η G → volume (ReyZygmund.MathlibOnly.shadow G) < ∞ →
          (∀ᵐ x ∂volume, ReyZygmund.MathlibOnly.overlap G x < ∞) ∧
          (∀ (q : ℝ), 2 ≤ q →
            eLpNorm (fun x => (ReyZygmund.MathlibOnly.overlap G x).toReal) (ENNReal.ofReal q) volume ≤
              ENNReal.ofReal (C m (∑ i, d i) * η⁻¹ * q ^ (m - 1)) *
                (volume (ReyZygmund.MathlibOnly.shadow G)) ^ (1 / q)) ∧
          (∫⁻ x in ReyZygmund.MathlibOnly.shadow G, ENNReal.ofReal
            (Real.exp (c m (∑ i, d i) *
              Real.rpow (η * (ReyZygmund.MathlibOnly.overlap G x).toReal) (1 / ((m - 1 : ℕ) : ℝ))) - 1)
              ∂volume) ≤ ENNReal.ofReal (C m (∑ i, d i)) * volume (ReyZygmund.MathlibOnly.shadow G))) := by
  obtain ⟨c, B, hc, hB, hexp⟩ := weaker_sparse_overlap_exponential
  let C (m D : ℕ) := momentConstant m D + B m D
  have hCpos (m D) : 0 < C m D := add_pos (momentConstant_pos m D) (hB m D)
  have hKC (m D) : momentConstant m D ≤ C m D := le_add_of_nonneg_right (hB m D).le
  have hBC (m D) : B m D ≤ C m D := le_add_of_nonneg_left (momentConstant_pos m D).le
  refine ⟨C, c, hCpos, hc, ?_⟩
  intro m d hm hd D G hG hweak
  have hG' : G ⊆ MathlibOnly.gridRectangles D := hG
  have hweak' := weak_containment_transfer G hweak
  constructor
  · intro p hp _hp2 f hf
    rw [MathlibOnly.Proof.maximal_eq_euclidean_of_memLp G f p hp hf]
    refine ⟨euclidean_weaker_grid_maximal_ae_finite hm hd D G hG' hweak' f p hp hf, ?_⟩
    have hn := euclidean_weaker_grid_maximal_eLpNorm hm hd D G hG' hweak' f p hp hf
    rw [← momentConstant_eq d] at hn
    exact hn.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (hKC m (∑ i, d i))
        (pow_nonneg (div_nonneg (zero_lt_one.trans hp).le (sub_pos.mpr hp).le) _))) _)
  · intro eta heta _heta1 hsparse hshadow
    obtain ⟨E, hE, hEdis⟩ := hsparse
    have hEmeas := fun R hR => (hE R hR).1
    have hEsub : ∀ R ∈ G, E R ⊆ ReyZygmund.MathlibOnly.rectangle R :=
      fun R hR => (hE R hR).2.1
    have hEmass : ∀ R ∈ G,
        ENNReal.ofReal eta * volume (ReyZygmund.MathlibOnly.rectangle R) ≤
          volume (E R) := fun R hR => (hE R hR).2.2
    simp only [rectangle_eq_flatProductBox] at hEsub hEmass
    rw [shadow_eq] at hshadow
    rw [overlap_eq, shadow_eq]
    refine ⟨weaker_sparse_overlap_ae_finite hm hd D G hG' hweak' eta heta E
      hEmeas hEsub hEdis hEmass hshadow, ?_, ?_⟩
    · intro q hq
      have hn := weaker_sparse_overlap_eLpNorm hm hd D G hG' hweak' eta heta E
        hEmeas hEsub hEdis hEmass hshadow q hq
      rw [← momentConstant_eq d] at hn
      exact hn.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hKC m (∑ i, d i)) (inv_nonneg.mpr heta.le))
          (pow_nonneg (by linarith : 0 ≤ q) _))) _)
    · exact (hexp m d hm hd D G hG' hweak' eta heta E hEmeas hEsub hEdis hEmass hshadow).trans
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal (hBC m (∑ i, d i))) _)

/-- Sparse overlap for incomparable families, with real-order moments and
constants depending only on the number of factors and total dimension. -/
theorem incomparable_overlap_theorem :
    ∃ C c : ℕ → ℕ → ℝ,
    (∀ m D, 0 < C m D) ∧ (∀ m D, 0 < c m D) ∧
    ∀ (m : ℕ) (d : Fin m → ℕ), 2 ≤ m → (∀ i : Fin m, 0 < d i) →
      ∀ (D : ∀ i : Fin m, ReyZygmund.MathlibOnly.CubeGrid (d i))
        (G : Set (∀ i : Fin m, Box (Fin (d i)))),
        G ⊆ ReyZygmund.MathlibOnly.gridRectangles D →
        (∀ R ∈ G, ∀ S ∈ G, ReyZygmund.MathlibOnly.rectangle R ⊆ ReyZygmund.MathlibOnly.rectangle S → R = S) →
        ∀ (η : ℝ), 0 < η → η ≤ 1 → ReyZygmund.MathlibOnly.Sparse η G → volume (ReyZygmund.MathlibOnly.shadow G) < ∞ →
          (∀ᵐ x ∂volume, ReyZygmund.MathlibOnly.overlap G x < ∞) ∧
          (∀ (q : ℝ), 2 ≤ q →
            eLpNorm (fun x => (ReyZygmund.MathlibOnly.overlap G x).toReal) (ENNReal.ofReal q) volume ≤
              ENNReal.ofReal (C m (∑ i, d i) * η⁻¹ * q ^ (m - 1)) *
                (volume (ReyZygmund.MathlibOnly.shadow G)) ^ (1 / q)) ∧
          (∫⁻ x in ReyZygmund.MathlibOnly.shadow G, ENNReal.ofReal
            (Real.exp (c m (∑ i, d i) *
              Real.rpow (η * (ReyZygmund.MathlibOnly.overlap G x).toReal) (1 / ((m - 1 : ℕ) : ℝ))) - 1)
              ∂volume) ≤ ENNReal.ofReal (C m (∑ i, d i)) * volume (ReyZygmund.MathlibOnly.shadow G) := by
  obtain ⟨C, c, hC, hc, hweak⟩ := weaker_containment_theorem
  refine ⟨C, c, hC, hc, ?_⟩
  intro m d hm hd D G hG hinc eta heta heta1 hsparse hshadow
  have hweaker : ∀ R ∈ G, ∀ S ∈ G,
      ReyZygmund.MathlibOnly.rectangle R ⊆
        ReyZygmund.MathlibOnly.rectangle S → ∃ i, R i = S i := by
    intro R hR S hS hRS
    have heq := hinc R hR S hS hRS
    exact ⟨⟨0, by omega⟩, congrFun heq _⟩
  exact (hweak m d hm hd D G hG hweaker).2 eta heta heta1 hsparse hshadow

end ReyZygmund.Main
