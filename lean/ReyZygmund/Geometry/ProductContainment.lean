import ReyZygmund.Geometry.ProductSteps

/-! # Containment of the product rectangles

Every coordinate box is nonempty. Consequently the coordinatewise order
used by the finite proofs is exactly inclusion of the product sets.
-/

open BoxIntegral
open scoped Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

theorem productBox_subset_iff (Q R : ∀ i, Box (Fin (d i))) :
    productBox Q ⊆ productBox R ↔ ∀ i, Q i ≤ R i := by
  constructor
  · intro h i
    change (Q i : Set (Fin (d i) → ℝ)) ⊆ R i
    intro y hy
    let x : ProductPoint d := Function.update (fun j => (Q j).upper) i y
    have hx : x ∈ productBox Q := by
      apply (mem_productBox Q x).mpr
      intro j
      by_cases hji : j = i
      · subst j
        simpa only [x, Function.update_self, Box.mem_coe] using hy
      · simpa only [x, Function.update_of_ne hji] using (Q j).upper_mem
    have hi := (mem_productBox R x).mp (h hx) i
    simpa only [x, Function.update_self, Box.mem_coe] using hi
  · intro h x hx
    exact (mem_productBox R x).mpr (fun i => h i ((mem_productBox Q x).mp hx i))

theorem productBox_injective : Function.Injective (productBox (d := d)) := by
  intro Q R h
  funext i
  exact le_antisymm ((productBox_subset_iff Q R).mp h.subset i)
    ((productBox_subset_iff R Q).mp h.symm.subset i)

end ReyZygmund.Geometry
