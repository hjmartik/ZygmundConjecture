import ReyZygmund.Geometry.ProductOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Product coordinates and Euclidean coordinates

The coordinate identification is a measurable equivalence preserving Lebesgue
measure. The finite-product calculation includes empty products and
zero-dimensional factors.

-/

open MeasureTheory
open scoped BigOperators

namespace ReyZygmund.Geometry

variable {m : ℕ} (d : Fin m → ℕ)

/-- List block coordinates in their usual consecutive order. -/
noncomputable def flattenCoordinates :
    ProductPoint d ≃ᵐ (Fin (∑ i, d i) → ℝ) :=
  (MeasurableEquiv.piCurry (fun (i : Fin m) (_ : Fin (d i)) => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (∑ i, d i) => ℝ)
      (finSigmaFinEquiv (n := d)))

theorem flattenCoordinates_apply (x : ProductPoint d) (i : Fin m) (k : Fin (d i)) :
    flattenCoordinates d x (finSigmaFinEquiv ⟨i, k⟩) = x i k := by
  exact MeasurableEquiv.piCongrLeft_apply_apply (finSigmaFinEquiv (n := d))
    (β := fun _ : Fin (∑ i, d i) => ℝ)
    (fun q => x q.1 q.2) ⟨i, k⟩

/-- Regrouping finite scalar Lebesgue factors preserves the product measure. -/
theorem volume_preserving_uncurry :
    MeasurePreserving
      (MeasurableEquiv.piCurry (fun (i : Fin m) (_ : Fin (d i)) => ℝ)).symm
      volume volume := by
  let u := (MeasurableEquiv.piCurry (fun (i : Fin m) (_ : Fin (d i)) => ℝ)).symm
  refine ⟨u.measurable, ?_⟩
  change volume.map u = Measure.pi (fun _ : (i : Fin m) × Fin (d i) =>
    (volume : Measure ℝ))
  refine (Measure.pi_eq (fun s _ => ?_)).symm
  rw [MeasurableEquiv.map_apply]
  have hset : u ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun k => s ⟨i, k⟩)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, u, MeasurableEquiv.coe_piCurry_symm,
      Sigma.uncurry, Sigma.forall]
  rw [hset, volume_pi_pi]
  simp_rw [volume_pi_pi]
  exact (Fintype.prod_sigma (fun q : (i : Fin m) × Fin (d i) => volume (s q))).symm

/-- The concrete coordinate map preserves Lebesgue measure exactly. -/
theorem volume_preserving_flattenCoordinates :
    MeasurePreserving (flattenCoordinates d) volume volume := by
  exact (volume_preserving_uncurry d).trans
    (volume_measurePreserving_piCongrLeft (fun _ : Fin (∑ i, d i) => ℝ)
      (finSigmaFinEquiv (n := d)))

end ReyZygmund.Geometry
