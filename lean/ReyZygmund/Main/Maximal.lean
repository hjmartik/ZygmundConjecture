import ReyZygmund.Maximal.Euclidean
import Verification.Challenges.Maximal

/-! # The incomparable maximal estimate

We prove the independently stated incomparable maximal estimate. For `f` in `L^p`,
local integrability identifies the nonnegative integrals in that statement with
the integrals used in the proof. The constant depends only on the number of
parameters and the total dimension.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry
namespace Main

private theorem challenge_rectangle_eq {m : ℕ} {d : Fin m → ℕ}
    (Q : ∀ i, Box (Fin (d i))) :
    ReyZygmundVerification.Challenges.rectangle Q =
      (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) := by
  ext x
  obtain ⟨y, rfl⟩ := (flattenCoordinates d).surjective x
  apply Iff.trans _ (mem_flatProductBox Q y).symm
  simp only [ReyZygmundVerification.Challenges.rectangle, Set.mem_ofPred_eq,
    mem_productBox, flattenCoordinates_apply]
  rfl

/-- Local integrability identifies the challenge's nonnegative mean
with the implementation's real absolute mean, before taking the supremum. -/
theorem challenge_absoluteMaximal_eq {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i))))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    ReyZygmundVerification.Challenges.absoluteMaximal G f =
      euclideanFamilyMaximal G f := by
  funext x
  unfold ReyZygmundVerification.Challenges.absoluteMaximal euclideanFamilyMaximal
  congr 1
  funext Q
  rw [challenge_rectangle_eq]
  have hv : volume (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)) < ∞ := by
    rw [volume_flatProductBox]
    exact productBox_volume_lt_top Q.1
  have hvpos : 0 < volume.real (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)) := by
    rw [Measure.real, volume_flatProductBox]
    exact productBox_volume_pos Q.1
  let : IsFiniteMeasure (volume.restrict
      (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ))) := isFiniteMeasure_restrict.mpr hv.ne
  have hlocal : IntegrableOn f
      (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ)) volume :=
    MemLp.integrable (by simpa using ENNReal.ofReal_le_ofReal hp.le)
      (hf.restrict _)
  by_cases hx : x ∈ (flatProductBox Q.1 : Set (Fin (∑ i, d i) → ℝ))
  · simp only [Set.indicator_of_mem hx]
    rw [ENNReal.ofReal_div_of_pos hvpos,
      ofReal_integral_eq_lintegral_ofReal hlocal.abs (Filter.Eventually.of_forall
        (fun y => abs_nonneg (f y))), Measure.real, ENNReal.ofReal_toReal hv.ne]
  · simp only [Set.indicator_of_notMem hx, ENNReal.ofReal_zero]

private noncomputable def dimensionalConstant (m D : ℕ) : ℝ :=
  (2 * (1 + ((m : ℝ) * (2 : ℝ) ^ m *
      ((2 : ℝ) ^ (6 * D + 10) + (2 : ℝ) ^ (m - 1))) *
    (1 + Real.sqrt ((m : ℝ) * (2 : ℝ) ^ (D + (m - 1)))))) ^ 2 + 3

/-- The independently reconstructed main statement is realized by the
concrete dyadic implementation, including the Euclidean operator. -/
theorem incomparable_maximal_theorem :
    ReyZygmundVerification.Challenges.incomparableMaximalStatement := by
  refine ⟨dimensionalConstant, ?_, ?_⟩
  · intro m D
    unfold dimensionalConstant
    positivity
  · intro m d hm hd D G hG hinc p hp f hf
    have hG' : G ⊆ Geometry.gridRectangles D := hG
    have hinc' : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → R = S := by
      intro R hR S hS hRS
      apply hinc R hR S hS
      rw [challenge_rectangle_eq, challenge_rectangle_eq]
      intro x hx
      obtain ⟨y, rfl⟩ := (flattenCoordinates d).surjective x
      exact (mem_flatProductBox S y).mpr (hRS ((mem_flatProductBox R y).mp hx))
    rw [challenge_absoluteMaximal_eq G f p hp hf]
    exact ⟨euclidean_grid_maximal_ae_finite hm hd D G hG' hinc' f p hp hf,
      euclidean_grid_maximal_eLpNorm hm hd D G hG' hinc' f p hp hf⟩

end Main
end ReyZygmund
