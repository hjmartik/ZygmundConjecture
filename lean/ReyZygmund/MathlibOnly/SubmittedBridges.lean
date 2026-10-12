import ReyZygmund.MathlibOnly.SubmittedDefinitions
import ReyZygmund.MathlibOnly.OperatorBridge
import ReyZygmund.Geometry.ProductContainment
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Identifications and exponential normalization for the main statements

Unlike the independent specifications, this proof module may import the
implementation. The geometric equivalence below needs no grid or dimension
restriction. The exponential conversion increases only the allowed constant.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.MathlibOnly.Submitted

theorem rectangle_subset_iff {m : ℕ} {d : Fin m → ℕ}
    (R S : ∀ i, Box (Fin (d i))) :
    rectangle R ⊆ rectangle S ↔ ∀ i, R i ≤ S i := by
  rw [rectangle_eq_flat, rectangle_eq_flat]
  have h : (Geometry.flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ⊆
      Geometry.flatProductBox S ↔ Geometry.productBox R ⊆ Geometry.productBox S := by
    constructor
    · intro h x hx
      exact (Geometry.mem_flatProductBox S x).mp
        (h ((Geometry.mem_flatProductBox R x).mpr hx))
    · intro h x hx
      obtain ⟨y, rfl⟩ := (Geometry.flattenCoordinates d).surjective x
      exact (Geometry.mem_flatProductBox S y).mpr
        (h ((Geometry.mem_flatProductBox R y).mp hx))
  exact h.trans (Geometry.productBox_subset_iff R S)

/-- Weak incomparability is equivalent to the condition
that containment leaves a factor unchanged. -/
theorem weaklyIncomparable_iff_equalFactor {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i)))) :
    WeaklyIncomparable G ↔ HasEqualFactorOnContainment G := by
  constructor
  · intro h R hR S hS hRS
    by_contra! hne
    exact h R hR S hS (fun i =>
      lt_of_le_of_ne ((rectangle_subset_iff R S).mp hRS i) (hne i))
  · intro h R hR S hS hstrict
    obtain ⟨i, hi⟩ := h R hR S hS
      ((rectangle_subset_iff R S).mpr (fun i => (hstrict i).le))
    exact (ne_of_lt (hstrict i)) hi

/-- Restore the constant term in an exponential integral. No measurability
of `v` is needed because the added integrand is the measurable constant one. -/
theorem lintegral_exp_le_add_one {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) (v : α → ℝ) (hv : ∀ x, 0 ≤ v x)
    (C : ℝ) (hC : 0 ≤ C)
    (h : (∫⁻ x in s, ENNReal.ofReal (Real.exp (v x)) - 1 ∂μ) ≤
      ENNReal.ofReal C * μ s) :
    (∫⁻ x in s, ENNReal.ofReal (Real.exp (v x)) ∂μ) ≤
      ENNReal.ofReal (C + 1) * μ s := by
  have hpoint (x) : ENNReal.ofReal (Real.exp (v x)) =
      (ENNReal.ofReal (Real.exp (v x)) - 1) + 1 := by
    apply (tsub_add_cancel_of_le _).symm
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr (hv x))
  calc
    (∫⁻ x in s, ENNReal.ofReal (Real.exp (v x)) ∂μ) =
        (∫⁻ x in s, (ENNReal.ofReal (Real.exp (v x)) - 1) + 1 ∂μ) :=
      lintegral_congr hpoint
    _ = (∫⁻ x in s, ENNReal.ofReal (Real.exp (v x)) - 1 ∂μ) + μ s := by
      rw [lintegral_add_right _ measurable_const]
      simp
    _ ≤ ENNReal.ofReal C * μ s + μ s := add_le_add h le_rfl
    _ = ENNReal.ofReal (C + 1) * μ s := by
      rw [ENNReal.ofReal_add hC zero_le_one, ENNReal.ofReal_one, add_mul, one_mul]

end ReyZygmund.MathlibOnly.Submitted
