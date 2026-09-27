import ReyZygmund.Selection.Endpoint
import ReyZygmund.Maximal.EndpointExhaustion

/-! # The full rounded endpoint

The finite shadow estimate passes to the countable grid family.
Constants are made uniform over dimension vectors of a fixed total by a
finite sum. This leaves the side function, grid, input and level arbitrary.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Continuous

open Geometry Overlap Selection

/-- The rounded endpoint is uniform in the monotone side function and every
product grid. The constant is chosen before the positive block
dimension vector with the prescribed total dimension. -/
theorem rounded_grid_endpoint_theorem (n totalDim : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
      ∀ (D : ∀ i, DyadicGrid (d i))
        (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)), Monotone phi →
      ∀ (f : (Fin (∑ i, d i) → ℝ) → ℝ), LocallyIntegrable f volume →
      ∀ (lam : ℝ), 0 < lam →
      volume {x | ENNReal.ofReal lam < euclideanFamilyMaximal
        (roundedGridRectangles D phi) f x} ≤
        ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
          (|f x| / lam * (Real.log (Real.exp 1 + |f x| / lam)) ^ (n - 1)) := by
  let C0 : (Fin (n + 1) → ℕ) → ℝ := fun d =>
    if hd : ∀ i, 0 < d i then (finite_rounded_endpoint_shadow n d hn hd).choose else 1
  have hC0 (d : Fin (n + 1) → ℕ) : 0 < C0 d := by
    by_cases hd : ∀ i, 0 < d i
    · simpa only [C0, dite_eq_left hd] using (finite_rounded_endpoint_shadow n d hn hd).choose_spec.1
    · simp only [C0, dite_eq_right hd, zero_lt_one]
  let C : ℝ := ∑ q : Fin (n + 1) → Fin (totalDim + 1), C0 (fun i => (q i).val)
  have hC : 0 < C := Finset.sum_pos (fun q _ => hC0 _) Finset.univ_nonempty
  refine ⟨C, hC, ?_⟩
  intro d hd hsum D phi hphi f hf lam hlam
  have hdi (i : Fin (n + 1)) : d i ≤ totalDim := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
  let q : Fin (n + 1) → Fin (totalDim + 1) := fun i => ⟨d i, Nat.lt_succ_of_le (hdi i)⟩
  have hbound : C0 d ≤ C :=
    Finset.single_le_sum (fun r _ => (hC0 (fun i => (r i).val)).le) (Finset.mem_univ q)
  apply euclidean_levelset_measure_le_of_finite_shadows (roundedGridRectangles D phi)
    ((countable_gridRectangles D).mono (roundedGridRectangles_subset D phi)) f lam hlam
  intro F hF hlevel
  have hfinite := (finite_rounded_endpoint_shadow n d hn hd).choose_spec.2
    D phi hphi f hf lam hlam F hF hlevel
  have hC0eq : C0 d = (finite_rounded_endpoint_shadow n d hn hd).choose := dite_eq_left hd
  rw [← hC0eq] at hfinite
  exact hfinite.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hbound) _)

end ReyZygmund.Continuous
