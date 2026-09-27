import ReyZygmund.Main.Maximal
import ReyZygmund.Maximal.WeakerGlobal
import ReyZygmund.Overlap.Exponential
import Verification.Challenges.Overlap

/-! # Sparse overlap and weaker containment

We prove the maximal and overlap estimates under the weaker containment condition,
then deduce the incomparable case. Pointwise identities for the rectangles, shadow
and overlap give the independently stated results.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Main

open Geometry Overlap

private theorem rectangle_eq {m : ℕ} {d : Fin m → ℕ}
    (R : ∀ i, Box (Fin (d i))) :
    ReyZygmundVerification.Challenges.rectangle R =
      (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) := by
  ext x
  obtain ⟨y, rfl⟩ := (flattenCoordinates d).surjective x
  apply Iff.trans _ (mem_flatProductBox R y).symm
  simp only [ReyZygmundVerification.Challenges.rectangle, Set.mem_ofPred_eq,
    mem_productBox, flattenCoordinates_apply]
  rfl

private theorem shadow_eq {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i)))) :
    ReyZygmundVerification.Challenges.shadow G = shadow G := by
  ext x
  simp only [ReyZygmundVerification.Challenges.shadow, shadow,
    rectangle_eq, Set.mem_iUnion, Subtype.exists]

private theorem overlap_eq {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i)))) :
    ReyZygmundVerification.Challenges.overlap G = overlap G := by
  funext x
  simp only [ReyZygmundVerification.Challenges.overlap, overlap, rectangle_eq]

private theorem weak_containment_transfer {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i))))
    (hweak : ∀ R ∈ G, ∀ S ∈ G,
      ReyZygmundVerification.Challenges.rectangle R ⊆
        ReyZygmundVerification.Challenges.rectangle S → ∃ i, R i = S i) :
    ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → ∃ i, R i = S i := by
  intro R hR S hS hRS
  apply hweak R hR S hS
  rw [rectangle_eq, rectangle_eq]
  intro x hx
  obtain ⟨y, rfl⟩ := (flattenCoordinates d).surjective x
  exact (mem_flatProductBox S y).mpr (hRS ((mem_flatProductBox R y).mp hx))

/-- Full source weaker-containment theorem: the maximal bound needs no
sparsity or finite shadow; the two overlap conclusions have precisely those
additional hypotheses. -/
theorem weaker_containment_theorem :
    ReyZygmundVerification.Challenges.weakerContainmentStatement := by
  obtain ⟨c, B, hc, hB, hexp⟩ := weaker_sparse_overlap_exponential
  let C (m D : ℕ) := momentConstant m D + B m D
  have hCpos (m D) : 0 < C m D := add_pos (momentConstant_pos m D) (hB m D)
  have hKC (m D) : momentConstant m D ≤ C m D := le_add_of_nonneg_right (hB m D).le
  have hBC (m D) : B m D ≤ C m D := le_add_of_nonneg_left (momentConstant_pos m D).le
  refine ⟨C, c, hCpos, hc, ?_⟩
  intro m d hm hd D G hG hweak
  have hG' : G ⊆ Geometry.gridRectangles D := hG
  have hweak' := weak_containment_transfer G hweak
  constructor
  · intro p hp _hp2 f hf
    rw [challenge_absoluteMaximal_eq G f p hp hf]
    refine ⟨euclidean_weaker_grid_maximal_ae_finite hm hd D G hG' hweak' f p hp hf, ?_⟩
    have hn := euclidean_weaker_grid_maximal_eLpNorm hm hd D G hG' hweak' f p hp hf
    rw [← momentConstant_eq d] at hn
    exact hn.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (hKC m (∑ i, d i))
        (pow_nonneg (div_nonneg (zero_lt_one.trans hp).le (sub_pos.mpr hp).le) _))) _)
  · intro eta heta _heta1 hsparse hshadow
    obtain ⟨E, hEmeas, hEsub, hEdis, hEmass⟩ := hsparse
    simp only [rectangle_eq] at hEsub hEmass
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

/-- The paper's incomparable-overlap theorem, with independently reconstructed
overlap, real-q moments and dimension-uniform exponential constants. -/
theorem incomparable_overlap_theorem :
    ReyZygmundVerification.Challenges.incomparableOverlapStatement := by
  obtain ⟨C, c, hC, hc, hweak⟩ := weaker_containment_theorem
  refine ⟨C, c, hC, hc, ?_⟩
  intro m d hm hd D G hG hinc eta heta heta1 hsparse hshadow
  have hweaker : ∀ R ∈ G, ∀ S ∈ G,
      ReyZygmundVerification.Challenges.rectangle R ⊆
        ReyZygmundVerification.Challenges.rectangle S → ∃ i, R i = S i := by
    intro R hR S hS hRS
    have heq := hinc R hR S hS hRS
    exact ⟨⟨0, by omega⟩, congrFun heq _⟩
  exact (hweak m d hm hd D G hG hweaker).2 eta heta heta1 hsparse hshadow

end ReyZygmund.Main
