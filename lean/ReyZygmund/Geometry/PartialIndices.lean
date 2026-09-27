import ReyZygmund.Geometry.ProductSteps

/-! # Finite cube indices in selected coordinates

Fix each unselected coordinate at its top cube. Each partial tuple is then counted
once, including for the empty coordinate set. A zero depth in an unused coordinate
causes no empty index set.

-/

noncomputable section

open BoxIntegral
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- Interior cubes in selected coordinates, with top cubes in the others. -/
def partialInterior (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A : Finset (Fin m)) : Finset (∀ i, Box (Fin (d i))) :=
  Fintype.piFinset (fun i => if i ∈ A then interior (I i) (N i) else {I i})

@[simp] theorem partialInterior_empty (I : ∀ i, Box (Fin (d i)))
    (N : Fin m → ℕ) : partialInterior I N ∅ = {I} := by
  simp [partialInterior, Fintype.piFinset_singleton]

theorem partialInterior_mem_selected {I : ∀ i, Box (Fin (d i))}
    {N : Fin m → ℕ} {A : Finset (Fin m)} {Q : ∀ i, Box (Fin (d i))}
    (hQ : Q ∈ partialInterior I N A) {i : Fin m} (hi : i ∈ A) :
    Q i ∈ interior (I i) (N i) := by
  simpa only [hi, ite_true] using Fintype.mem_piFinset.mp hQ i

theorem partialInterior_mem_unselected {I : ∀ i, Box (Fin (d i))}
    {N : Fin m → ℕ} {A : Finset (Fin m)} {Q : ∀ i, Box (Fin (d i))}
    (hQ : Q ∈ partialInterior I N A) {i : Fin m} (hi : i ∉ A) : Q i = I i := by
  simpa only [hi, ite_false, Finset.mem_singleton] using Fintype.mem_piFinset.mp hQ i

/-- Adding one coordinate is a bijective reindexing of the finite sum. -/
theorem sum_partialInterior_insert {V : Type*} [AddCommMonoid V]
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (A : Finset (Fin m))
    (j : Fin m) (hj : j ∉ A) (H : (∀ i, Box (Fin (d i))) → V) :
    (∑ L ∈ partialInterior I N (insert j A), H L) =
      ∑ Q ∈ interior (I j) (N j),
        ∑ K ∈ partialInterior I N A, H (Function.update K j Q) := by
  symm
  rw [← Finset.sum_product (interior (I j) (N j)) (partialInterior I N A)
    (fun pair => H (Function.update pair.2 j pair.1))]
  apply Finset.sum_bij (fun pair _ => Function.update pair.2 j pair.1)
  · intro pair hpair
    obtain ⟨hQ, hK⟩ := Finset.mem_product.mp hpair
    apply Fintype.mem_piFinset.mpr
    intro i
    by_cases hij : i = j
    · subst i
      simpa only [Finset.mem_insert_self, ite_true, Function.update_self] using hQ
    · have hKi := Fintype.mem_piFinset.mp hK i
      simpa only [Finset.mem_insert, hij, false_or, Function.update_of_ne hij] using hKi
  · intro a ha b hb heq
    have hQ : a.1 = b.1 := by simpa using congrFun heq j
    have hK : a.2 = b.2 := by
      funext i
      by_cases hij : i = j
      · subst i
        rw [partialInterior_mem_unselected (Finset.mem_product.mp ha).2 hj,
          partialInterior_mem_unselected (Finset.mem_product.mp hb).2 hj]
      · simpa only [Function.update_of_ne hij] using congrFun heq i
    exact Prod.ext hQ hK
  · intro L hL
    have hQ : L j ∈ interior (I j) (N j) :=
      partialInterior_mem_selected hL (Finset.mem_insert_self j A)
    have hK : Function.update L j (I j) ∈ partialInterior I N A := by
      apply Fintype.mem_piFinset.mpr
      intro i
      by_cases hij : i = j
      · subst i
        simp only [hj, ite_false, Function.update_self, Finset.mem_singleton]
      · have hLi := Fintype.mem_piFinset.mp hL i
        simpa only [Finset.mem_insert, hij, false_or, Function.update_of_ne hij] using hLi
    exact ⟨(L j, Function.update L j (I j)), Finset.mem_product.mpr ⟨hQ, hK⟩, by simp⟩
  · intro _ _
    rfl

end ReyZygmund.Geometry
