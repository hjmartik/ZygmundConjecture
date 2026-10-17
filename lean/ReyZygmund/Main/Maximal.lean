import ReyZygmund.Maximal.WeakerGlobal
import ReyZygmund.MathlibOnly.Proof.OperatorBridge

/-! # The incomparable maximal estimate

The incomparable maximal estimate follows from the weakly incomparable estimate.
For `L^p` inputs, local integrability identifies the real and nonnegative averages.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry MathlibOnly.Proof
namespace Main

private noncomputable def dimensionalConstant (m D : ℕ) : ℝ :=
  (2 * (1 + ((m : ℝ) * (2 : ℝ) ^ m *
      ((2 : ℝ) ^ (6 * D + 10) + (2 : ℝ) ^ (m - 1))) *
    (1 + Real.sqrt ((m : ℝ) * (2 : ℝ) ^ (D + (m - 1)))))) ^ 2 + 3

/-- The maximal estimate for incomparable dyadic families, for `p > 1`,
with a constant depending only on the number of factors and total dimension. -/
theorem incomparable_maximal_theorem :
    ∃ C : ℕ → ℕ → ℝ, (∀ m D, 0 < C m D) ∧
    ∀ (m : ℕ) (d : Fin m → ℕ), 2 ≤ m → (∀ i : Fin m, 0 < d i) →
      ∀ (D : ∀ i : Fin m, ReyZygmund.MathlibOnly.CubeGrid (d i))
        (G : Set (∀ i : Fin m, Box (Fin (d i)))),
        G ⊆ ReyZygmund.MathlibOnly.gridRectangles D →
        (∀ R ∈ G, ∀ S ∈ G, ReyZygmund.MathlibOnly.rectangle R ⊆ ReyZygmund.MathlibOnly.rectangle S → R = S) →
        ∀ (p : ℝ), 1 < p →
          ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ),
            MemLp f (ENNReal.ofReal p) volume →
            (∀ᵐ x ∂volume, ReyZygmund.MathlibOnly.maximal G f x < ∞) ∧
              eLpNorm (fun x => (ReyZygmund.MathlibOnly.maximal G f x).toReal)
                  (ENNReal.ofReal p) volume ≤
                ENNReal.ofReal (C m (∑ i, d i) * (p / (p - 1)) ^ (m - 1)) *
                  eLpNorm f (ENNReal.ofReal p) volume := by
  refine ⟨dimensionalConstant, ?_, ?_⟩
  · intro m D
    unfold dimensionalConstant
    positivity
  · intro m d hm hd D G hG hinc p hp f hf
    have hG' : G ⊆ MathlibOnly.gridRectangles D := hG
    have hinc' : ∀ R ∈ G, ∀ S ∈ G, productRectangle R ⊆ productRectangle S → R = S := by
      intro R hR S hS hRS
      apply hinc R hR S hS
      rw [Geometry.rectangle_eq_flatProductBox, Geometry.rectangle_eq_flatProductBox]
      intro x hx
      obtain ⟨y, rfl⟩ := (flattenCoordinates d).surjective x
      exact (mem_flatProductBox S y).mpr (hRS ((mem_flatProductBox R y).mp hx))
    rw [maximal_eq_euclidean_of_memLp G f p hp hf]
    have hweak : ∀ R ∈ G, ∀ S ∈ G,
        productRectangle R ⊆ productRectangle S → ∃ i, R i = S i := by
      intro R hR S hS hRS
      exact ⟨⟨0, by omega⟩, congrFun (hinc' R hR S hS hRS) _⟩
    exact ⟨euclidean_weaker_grid_maximal_ae_finite hm hd D G hG' hweak f p hp hf,
      euclidean_weaker_grid_maximal_eLpNorm hm hd D G hG' hweak f p hp hf⟩

end Main
end ReyZygmund
