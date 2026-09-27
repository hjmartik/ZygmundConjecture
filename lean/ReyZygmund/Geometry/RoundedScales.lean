import ReyZygmund.Geometry.Rounding
import ReyZygmund.Geometry.GridOrder
import ReyZygmund.Geometry.GridFamilies
import Mathlib.Data.Fin.Tuple.Basic

/-!
# The image of the rounded side lengths

Positive sides and a positive-valued monotone function give the paper's
rounded scale set. It is an image, not an integer-valued graph: several last
scales may accompany the same first scales. Only strict order in every first
scale implies weak order in the last scale.
-/

open BoxIntegral

namespace ReyZygmund.Geometry

variable {n : ℕ}

/-- The image of rounding all first sides and the dependent last side. -/
noncomputable def roundedScales
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) :
    Set (Fin (n + 1) → ℤ) :=
  Set.range (fun s => Fin.snoc (fun i => roundedScale (s i).1) (roundedScale (phi s).1))

/-- The paper's strict-order property. No continuity or strict monotonicity
of the positive-valued function is assumed. -/
theorem roundedScales_order
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) (hphi : Monotone phi)
    {k l : Fin (n + 1) → ℤ} (hk : k ∈ roundedScales phi) (hl : l ∈ roundedScales phi)
    (hkl : ∀ i : Fin n, k i.castSucc < l i.castSucc) : k (Fin.last n) ≤ l (Fin.last n) := by
  obtain ⟨s, rfl⟩ := hk
  obtain ⟨t, rfl⟩ := hl
  have hst : s ≤ t := by
    intro i
    have hi : roundedScale (s i).1 < roundedScale (t i).1 := by
      simpa only [Fin.snoc_castSucc] using hkl i
    exact (lt_of_roundedScale_lt (t i).2 hi).le
  simpa only [Fin.snoc_last] using roundedScale_mono (phi s).2 (hphi hst)

/-- Rectangles in the specified grids whose side exponents belong to
the rounded image. Grid generations are negatives of side exponents. -/
noncomputable def roundedGridRectangles {d : Fin (n + 1) → ℕ}
    (D : ∀ i, DyadicGrid (d i))
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) :
    Set (∀ i, Box (Fin (d i))) :=
  {R | ∃ k ∈ roundedScales phi, ∀ i, R i ∈ (D i).cubes (-k i)}

theorem roundedGridRectangles_subset {d : Fin (n + 1) → ℕ}
    (D : ∀ i, DyadicGrid (d i))
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) :
    roundedGridRectangles D phi ⊆ gridRectangles D := by
  rintro R ⟨k, _, hR⟩ i
  exact ⟨-k i, hR i⟩

end ReyZygmund.Geometry
