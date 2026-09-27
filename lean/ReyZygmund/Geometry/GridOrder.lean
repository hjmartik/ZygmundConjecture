import ReyZygmund.Geometry.GridDescendants

/-! # Generation order and containment in a dyadic grid -/

open BoxIntegral

namespace ReyZygmund.Geometry.DyadicGrid

variable {d : ℕ} (D : DyadicGrid d)

/-- Intersecting grid cubes are contained in the direction of increasing
generation. The conclusion includes shared half-open boundary points. -/
theorem le_of_generation_le {n k : ℤ} {Q R : Box (Fin d)}
    (hQ : Q ∈ D.cubes n) (hR : R ∈ D.cubes k) (hnk : n ≤ k)
    {x : Fin d → ℝ} (hxQ : x ∈ Q) (hxR : x ∈ R) : R ≤ Q := by
  have hindex : n + ((k - n).toNat : ℤ) = k := by omega
  have hlocal : R ∈ level Q (k - n).toNat :=
    D.mem_level_of_mem_point hQ (by simpa only [hindex] using hR) hxQ hxR
  exact (level Q _).le_of_mem hlocal

theorem nested_of_common_point {n k : ℤ} {Q R : Box (Fin d)}
    (hQ : Q ∈ D.cubes n) (hR : R ∈ D.cubes k)
    {x : Fin d → ℝ} (hxQ : x ∈ Q) (hxR : x ∈ R) : Q ≤ R ∨ R ≤ Q := by
  rcases le_total n k with h | h
  · exact Or.inr (D.le_of_generation_le hQ hR h hxQ hxR)
  · exact Or.inl (D.le_of_generation_le hR hQ h hxR hxQ)

/-- Strict containment forces a strict generation gap; no separate width
comparison or positive-dimension assumption is needed. -/
theorem generation_lt_of_containment_ne {n k : ℤ} {Q R : Box (Fin d)}
    (hQ : Q ∈ D.cubes n) (hR : R ∈ D.cubes k)
    (hQR : Q ≤ R) (hne : Q ≠ R) : k < n := by
  by_contra h
  have hRQ := D.le_of_generation_le hQ hR (le_of_not_gt h)
    Q.upper_mem (hQR Q.upper_mem)
  exact hne (le_antisymm hQR hRQ)

end ReyZygmund.Geometry.DyadicGrid
