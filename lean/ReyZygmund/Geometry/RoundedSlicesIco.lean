import ReyZygmund.Geometry.IcoGrid
import ReyZygmund.Geometry.LastCoordinate

/-! # Pointwise slices with lower-inclusive boundaries

Strict containment in all initial factors orders their rounded scales; the
last cubes are then nested through the fixed slice point. Incomparability
rules this out and also makes projection injective. Reindexing the extended
nonnegative sum gives the overlap identity for arbitrary set families.
-/

open BoxIntegral
open scoped BigOperators Classical ENNReal
open ReyZygmund.MathlibOnly

namespace ReyZygmund.Geometry

variable {n : ℕ} {d : Fin (n + 1) → ℕ}

private theorem rectangleIco_subset_of_factors {R S : Rectangle d}
    (h : ∀ i, cubeIco (R i) ⊆ cubeIco (S i)) : rectangleIco R ⊆ rectangleIco S := by
  intro x hx i j
  exact h i (fun k => hx i k) j

/-- The initial projection is injective on incomparable grid rectangles
through a fixed point, including points on lower cube faces. -/
theorem initialProjection_injOn_ico
    (D : ∀ i, CubeGrid (d i)) (G : Set (Rectangle d)) (hG : G ⊆ gridRectangles D)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, rectangleIco R ⊆ rectangleIco S → R = S)
    (t : Fin (d (Fin.last n)) → ℝ) :
    Set.InjOn initialProjection {R | R ∈ G ∧ t ∈ cubeIco (R (Fin.last n))} := by
  rintro R ⟨hR, htR⟩ S ⟨hS, htS⟩ heq
  have hfirst (i : Fin n) : R i.castSucc = S i.castSucc :=
    congrArg (fun P => P i) heq
  obtain ⟨k, hk⟩ := hG hR (Fin.last n)
  obtain ⟨l, hl⟩ := hG hS (Fin.last n)
  rcases (D (Fin.last n)).ico_nested_of_common_point hk hl htR htS with hlast | hlast
  · apply hinc R hR S hS
    apply rectangleIco_subset_of_factors
    exact fun i => Fin.lastCases hlast (fun j => by rw [hfirst j]) i
  · symm
    apply hinc S hS R hR
    apply rectangleIco_subset_of_factors
    exact fun i => Fin.lastCases hlast (fun j => by rw [hfirst j]) i

/-- Rounded order excludes strict containment in every initial factor of
two rectangles through the same last-coordinate point. -/
theorem sliceFamilyIco_weaklyIncomparable
    (hn : 0 < n) (D : ∀ i, CubeGrid (d i))
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) (hphi : Monotone phi)
    (G : Set (Rectangle d)) (hG : G ⊆ roundedGridRectangles D phi)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, rectangleIco R ⊆ rectangleIco S → R = S)
    (t : Fin (d (Fin.last n)) → ℝ) :
    ∀ P ∈ sliceFamilyIco G t, ∀ Q ∈ sliceFamilyIco G t,
      ¬ ∀ i, cubeIco (P i) ⊂ cubeIco (Q i) := by
  rintro P ⟨R, ⟨hR, htR⟩, rfl⟩ Q ⟨S, ⟨hS, htS⟩, rfl⟩ hstrict
  obtain ⟨k, hk, hRk⟩ := hG hR
  obtain ⟨l, hl, hSl⟩ := hG hS
  have hfirst (i : Fin n) : R i.castSucc ≤ S i.castSucc :=
    cubeIco_subset_iff.mp (hstrict i).subset
  have hne (i : Fin n) : R i.castSucc ≠ S i.castSucc := by
    intro hi
    exact (hstrict i).ne (congrArg cubeIco hi)
  have hkl (i : Fin n) : k i.castSucc < l i.castSucc := by
    have hi := (D i.castSucc).generation_lt_of_containment_ne
      (hRk i.castSucc) (hSl i.castSucc) (hfirst i) (hne i)
    omega
  have hlast := roundedScales_order phi hphi hk hl hkl
  have hlastSubset : cubeIco (R (Fin.last n)) ⊆ cubeIco (S (Fin.last n)) :=
    (D (Fin.last n)).ico_subset_of_scale_le
      (by simpa only [CubeGrid.cubesAtGeneration_neg] using hRk (Fin.last n))
      (by simpa only [CubeGrid.cubesAtGeneration_neg] using hSl (Fin.last n))
      hlast htR htS
  have heq : R = S := hinc R hR S hS (rectangleIco_subset_of_factors
    (fun i => Fin.lastCases hlastSubset (fun j => (hstrict j).subset) i))
  exact hne ⟨0, hn⟩ (congrArg (fun T => T (Fin.castSucc ⟨0, hn⟩)) heq)

/-- Every member of the lower-inclusive slice comes from exactly one
original rectangle through the fixed point. -/
theorem sliceFamilyIco_existsUnique
    (D : ∀ i, CubeGrid (d i)) (G : Set (Rectangle d)) (hG : G ⊆ gridRectangles D)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, rectangleIco R ⊆ rectangleIco S → R = S)
    (t : Fin (d (Fin.last n)) → ℝ)
    {P : Rectangle (fun i : Fin n => d i.castSucc)} (hP : P ∈ sliceFamilyIco G t) :
    ∃! R, R ∈ G ∧ t ∈ cubeIco (R (Fin.last n)) ∧ initialProjection R = P := by
  obtain ⟨R, ⟨hR, htR⟩, hRP⟩ := hP
  refine ⟨R, ⟨hR, htR, hRP⟩, ?_⟩
  rintro S ⟨hS, htS, hSP⟩
  exact initialProjection_injOn_ico D G hG hinc t
    ⟨hS, htS⟩ ⟨hR, htR⟩ (hSP.trans hRP.symm)

/-- Membership after concatenating the last block is the product of
membership in the projected rectangle and in the last cube. -/
theorem appendLastPoint_mem_rectangleIco (R : Rectangle d)
    (x : Point (fun i : Fin n => d i.castSucc)) (t : Fin (d (Fin.last n)) → ℝ) :
    appendLastPoint x t ∈ rectangleIco R ↔
      x ∈ rectangleIco (initialProjection R) ∧ t ∈ cubeIco (R (Fin.last n)) := by
  constructor
  · intro h
    exact ⟨fun i j => by simpa only [appendLastPoint_castSucc, initialProjection] using h i.castSucc j,
      fun j => by simpa only [appendLastPoint_last] using h (Fin.last n) j⟩
  · rintro ⟨hfirst, hlast⟩ i
    exact Fin.lastCases (fun j => by simpa only [appendLastPoint_last] using hlast j)
      (fun k j => by simpa only [appendLastPoint_castSucc, initialProjection] using hfirst k j) i

/-- The pointwise overlap identity for lower-inclusive slices. -/
theorem overlapIco_appendLastPoint
    (D : ∀ i, CubeGrid (d i)) (G : Set (Rectangle d)) (hG : G ⊆ gridRectangles D)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, rectangleIco R ⊆ rectangleIco S → R = S)
    (x : Point (fun i : Fin n => d i.castSucc)) (t : Fin (d (Fin.last n)) → ℝ) :
    overlapIco G (appendLastPoint x t) = overlapIco (sliceFamilyIco G t) x := by
  let U : Set (Rectangle d) := {R | R ∈ G ∧ t ∈ cubeIco (R (Fin.last n))}
  calc
    overlapIco G (appendLastPoint x t) =
        ∑' R : U, (rectangleIco (initialProjection R.1)).indicator
          (fun _ => (1 : ℝ≥0∞)) x := by
      rw [overlapIco, tsum_subtype G (fun R =>
        (rectangleIco R).indicator (fun _ => (1 : ℝ≥0∞)) (appendLastPoint x t)),
        tsum_subtype U (fun R => (rectangleIco (initialProjection R)).indicator
          (fun _ => (1 : ℝ≥0∞)) x)]
      apply tsum_congr
      intro R
      by_cases hR : R ∈ G
      · by_cases ht : t ∈ cubeIco (R (Fin.last n))
        · have hU : R ∈ U := ⟨hR, ht⟩
          rw [Set.indicator_of_mem hR, Set.indicator_of_mem hU]
          by_cases hx : x ∈ rectangleIco (initialProjection R)
          · rw [Set.indicator_of_mem ((appendLastPoint_mem_rectangleIco R x t).mpr ⟨hx, ht⟩),
              Set.indicator_of_mem hx]
          · rw [Set.indicator_of_notMem (fun h => hx
                ((appendLastPoint_mem_rectangleIco R x t).mp h).1), Set.indicator_of_notMem hx]
        · have hU : R ∉ U := fun h => ht h.2
          rw [Set.indicator_of_mem hR, Set.indicator_of_notMem hU,
            Set.indicator_of_notMem (fun h => ht
              ((appendLastPoint_mem_rectangleIco R x t).mp h).2)]
      · have hU : R ∉ U := fun h => hR h.1
        rw [Set.indicator_of_notMem hR, Set.indicator_of_notMem hU]
    _ = overlapIco (sliceFamilyIco G t) x := by
      symm
      exact tsum_image (fun P => (rectangleIco P).indicator (fun _ => (1 : ℝ≥0∞)) x)
        (initialProjection_injOn_ico D G hG hinc t)

end ReyZygmund.Geometry
