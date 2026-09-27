import ReyZygmund.Geometry.RoundedScales

/-!
# Containment in a slice of a rounded family

For an incomparable family, projection onto the first coordinates is injective on
rectangles through a fixed last-coordinate point. If this family is rounded from a
monotone side function, its projection satisfies the weaker containment property.
-/

open BoxIntegral

namespace ReyZygmund.Geometry

variable {n : ℕ} {d : Fin (n + 1) → ℕ}

/-- Delete the last coordinate cube from a rectangle. -/
def initialProjection (R : ∀ i, Box (Fin (d i))) :
    ∀ i : Fin n, Box (Fin (d i.castSucc)) := fun i => R i.castSucc

/-- The projected family above a fixed point of the last block. -/
def sliceFamily (G : Set (∀ i, Box (Fin (d i)))) (t : Fin (d (Fin.last n)) → ℝ) :
    Set (∀ i : Fin n, Box (Fin (d i.castSucc))) :=
  initialProjection '' {R | R ∈ G ∧ t ∈ R (Fin.last n)}

/-- No multiplicity is lost when passing to the slice of an incomparable
family in dyadic grids. -/
theorem initialProjection_injOn
    (D : ∀ i, DyadicGrid (d i)) (G : Set (∀ i, Box (Fin (d i))))
    (hG : G ⊆ gridRectangles D)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (t : Fin (d (Fin.last n)) → ℝ) :
    Set.InjOn initialProjection {R | R ∈ G ∧ t ∈ R (Fin.last n)} := by
  rintro R ⟨hR, htR⟩ S ⟨hS, htS⟩ heq
  have hfirst (i : Fin n) : R i.castSucc = S i.castSucc :=
    congrArg (fun P => P i) heq
  obtain ⟨k, hk⟩ := hG hR (Fin.last n)
  obtain ⟨l, hl⟩ := hG hS (Fin.last n)
  rcases (D (Fin.last n)).nested_of_common_point hk hl htR htS with hlast | hlast
  · apply hinc R hR S hS
    intro i
    exact Fin.lastCases hlast (fun j => (hfirst j).le) i
  · symm
    apply hinc S hS R hR
    intro i
    exact Fin.lastCases hlast (fun j => (hfirst j).symm.le) i

theorem sliceFamily_subset_grid
    (D : ∀ i, DyadicGrid (d i)) (G : Set (∀ i, Box (Fin (d i))))
    (hG : G ⊆ gridRectangles D) (t : Fin (d (Fin.last n)) → ℝ) :
    sliceFamily G t ⊆ gridRectangles (fun i : Fin n => D i.castSucc) := by
  rintro P ⟨R, ⟨hR, _⟩, rfl⟩ i
  exact hG hR i.castSucc

/-- Rounded order rules out strict containment in every first coordinate of
two rectangles through the same last-coordinate point. -/
theorem rounded_slice_containment
    (hn : 0 < n) (D : ∀ i, DyadicGrid (d i))
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) (hphi : Monotone phi)
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ roundedGridRectangles D phi)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (t : Fin (d (Fin.last n)) → ℝ)
    {R S : ∀ i, Box (Fin (d i))} (hR : R ∈ G) (hS : S ∈ G)
    (htR : t ∈ R (Fin.last n)) (htS : t ∈ S (Fin.last n))
    (hfirst : ∀ i : Fin n, R i.castSucc ≤ S i.castSucc) :
    ∃ i : Fin n, R i.castSucc = S i.castSucc := by
  classical
  by_contra h
  have hne : ∀ i : Fin n, R i.castSucc ≠ S i.castSucc := by simpa only [not_exists] using h
  obtain ⟨k, hk, hRk⟩ := hG hR
  obtain ⟨l, hl, hSl⟩ := hG hS
  have hkl : ∀ i : Fin n, k i.castSucc < l i.castSucc := by
    intro i
    have hi := (D i.castSucc).generation_lt_of_containment_ne
      (hRk i.castSucc) (hSl i.castSucc) (hfirst i) (hne i)
    omega
  have hlast := roundedScales_order phi hphi hk hl hkl
  have hlastSubset : R (Fin.last n) ≤ S (Fin.last n) :=
    (D (Fin.last n)).le_of_generation_le (hSl (Fin.last n)) (hRk (Fin.last n))
      (neg_le_neg hlast) htS htR
  have heq : R = S := hinc R hR S hS
    (fun i => Fin.lastCases hlastSubset hfirst i)
  exact hne ⟨0, hn⟩ (congrArg (fun P => P (Fin.castSucc ⟨0, hn⟩)) heq)

/-- The paper's weaker-containment hypothesis on the slice family. -/
theorem sliceFamily_weaker_containment
    (hn : 0 < n) (D : ∀ i, DyadicGrid (d i))
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) (hphi : Monotone phi)
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ roundedGridRectangles D phi)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (t : Fin (d (Fin.last n)) → ℝ) :
    ∀ P ∈ sliceFamily G t, ∀ Q ∈ sliceFamily G t,
      (∀ i, P i ≤ Q i) → ∃ i, P i = Q i := by
  rintro P ⟨R, ⟨hR, htR⟩, rfl⟩ Q ⟨S, ⟨hS, htS⟩, rfl⟩ hfirst
  exact rounded_slice_containment hn D phi hphi G hG hinc t hR hS htR htS hfirst

end ReyZygmund.Geometry
