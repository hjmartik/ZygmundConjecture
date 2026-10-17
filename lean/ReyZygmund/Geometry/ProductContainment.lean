import ReyZygmund.Geometry.ProductSteps

/-! # Containment of the product rectangles

Every coordinate box is nonempty. Consequently the coordinatewise order
used by the finite proofs is exactly inclusion of the product sets.
-/

open BoxIntegral
open scoped Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

theorem productRectangle_subset_iff (Q R : ∀ i, Box (Fin (d i))) :
    productRectangle Q ⊆ productRectangle R ↔ ∀ i, Q i ≤ R i := by
  constructor
  · intro h i
    change (Q i : Set (Fin (d i) → ℝ)) ⊆ R i
    intro y hy
    let x : ProductPoint d := Function.update (fun j => (Q j).upper) i y
    have hx : x ∈ productRectangle Q := by
      apply (mem_productRectangle Q x).mpr
      intro j
      by_cases hji : j = i
      · subst j
        simpa only [x, Function.update_self, Box.mem_coe] using hy
      · simpa only [x, Function.update_of_ne hji] using (Q j).upper_mem
    have hi := (mem_productRectangle R x).mp (h hx) i
    simpa only [x, Function.update_self, Box.mem_coe] using hi
  · intro h x hx
    exact (mem_productRectangle R x).mpr (fun i => h i ((mem_productRectangle Q x).mp hx i))

theorem productRectangle_injective : Function.Injective (productRectangle (d := d)) := by
  intro Q R h
  funext i
  exact le_antisymm ((productRectangle_subset_iff Q R).mp h.subset i)
    ((productRectangle_subset_iff R Q).mp h.symm.subset i)

/-- Weak incomparability says that coordinatewise containment leaves at least
one factor unchanged. -/
theorem weaklyIncomparable_iff_equal_factor
    (G : Set (∀ i, Box (Fin (d i)))) :
    MathlibOnly.WeaklyIncomparable G ↔
      ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → ∃ i, R i = S i := by
  change (∀ R ∈ G, ∀ S ∈ G, ¬ ∀ i, R i < S i) ↔ _
  constructor
  · intro h R hR S hS hRS
    by_contra! hne
    exact h R hR S hS (fun i => lt_of_le_of_ne (hRS i) (hne i))
  · intro h R hR S hS hstrict
    obtain ⟨i, hi⟩ := h R hR S hS (fun i => (hstrict i).le)
    exact (ne_of_lt (hstrict i)) hi

end ReyZygmund.Geometry
