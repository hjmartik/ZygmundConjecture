import ReyZygmund.MathlibOnly.OperatorBridge
import ReyZygmund.Continuous.Convention

/-! # Boundary conventions and measurability

For locally integrable input and arbitrary positions and side lengths, translation gives
pointwise equality of the maximal functions under the two half-open conventions.
For the countable rounded family, the equality holds outside one null set. The two
arguments distinguish countable from uncountable families.

-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace ReyZygmund.MathlibOnly

theorem continuous_maximal_eq_ico {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf : LocallyIntegrable f volume) :
    maximal (continuousRectangles d phi) f =
      Continuous.icoEuclideanFamilyMaximal (continuousRectangles d phi) f := by
  rw [continuousRectangles_eq, maximal_eq_endpoint _ f hf]
  exact (Continuous.continuous_maximal_convention_eq phi f hf).symm

theorem measurable_continuous_maximal {n : ℕ} {d : Fin (n + 1) → ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf : LocallyIntegrable f volume) :
    Measurable (maximal (continuousRectangles d phi) f) := by
  rw [continuousRectangles_eq, maximal_eq_endpoint _ f hf]
  exact Continuous.measurable_continuous_maximal phi f hf

theorem rounded_maximal_ae_eq_ico {n : ℕ} {d : Fin (n + 1) → ℕ}
    (tau : ∀ i, Fin (d i) → Fin 3)
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (hf : LocallyIntegrable f volume) :
    maximal (roundedRectangles tau phi) f =ᵐ[volume]
      Continuous.icoEuclideanFamilyMaximal (roundedRectangles tau phi) f := by
  rw [roundedRectangles_eq, maximal_eq_endpoint _ f hf]
  exact (Continuous.icoEuclideanFamilyMaximal_ae_eq _
    ((Geometry.countable_gridRectangles _).mono
      (Geometry.roundedGridRectangles_subset _ phi)) f).symm

end ReyZygmund.MathlibOnly
