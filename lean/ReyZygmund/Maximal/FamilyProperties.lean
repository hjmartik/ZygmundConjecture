import ReyZygmund.Maximal.Family
import ReyZygmund.Geometry.ProductIntegrability

/-! # Finite-family maximal functions on the smallest cubes

Membership in a retained rectangle is constant on each smallest product cube. The
family maximum therefore has this constancy even when the input does not. The
moment estimate here uses the ordinary product maximal bound, not the improved
incomparable estimate.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

private theorem productBox_membership_on_leaf
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (P Q : ∀ i, Box (Fin (d i))) (hP : P ∈ productLeaves I N)
    (hQ : Q ∈ productDescendants I N)
    (x y : ProductPoint d) (hx : x ∈ productBox P) (hy : y ∈ productBox P) :
    x ∈ productBox Q ↔ y ∈ productBox Q := by
  have hstep : ∀ i, x i ∈ Q i ↔ y i ∈ Q i := by
    intro i
    obtain ⟨n, hn, hQn⟩ := mem_descendants.mp (mem_productDescendants.mp hQ i)
    rcases level_le_or_disjoint hn (Fintype.mem_piFinset.mp hP i) hQn with hPQ | hdis
    · exact ⟨fun _ => hPQ ((mem_productBox P y).mp hy i),
        fun _ => hPQ ((mem_productBox P x).mp hx i)⟩
    · have hxQ : x i ∉ Q i := fun h =>
        Set.disjoint_left.mp hdis ((mem_productBox P x).mp hx i) h
      have hyQ : y i ∉ Q i := fun h =>
        Set.disjoint_left.mp hdis ((mem_productBox P y).mp hy i) h
      exact iff_of_false hxQ hyQ
  simp only [mem_productBox]
  exact forall_congr' hstep

theorem productLeafConstant_finiteFamilyMaximal
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (F : boundedMeasurableFunctions d) :
    ProductLeafConstant I N (finiteFamilyMaximal G F) := by
  intro P hP x hx y hy
  by_cases h : G.Nonempty
  · rw [finiteFamilyMaximal, dite_eq_left h, finiteFamilyMaximal, dite_eq_left h]
    apply Finset.sup'_congr _ rfl
    intro Q hQ
    have he := productBox_membership_on_leaf I N P Q hP (hG hQ) x y hx hy
    by_cases hxQ : x ∈ productBox Q
    · rw [Set.indicator_of_mem hxQ, Set.indicator_of_mem (he.mp hxQ)]
    · rw [Set.indicator_of_notMem hxQ, Set.indicator_of_notMem (mt he.mpr hxQ)]
  · simp [finiteFamilyMaximal, h]

theorem finiteFamilyMaximal_eq_zero_of_notMem_root
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) (hx : x ∉ productBox I) :
    finiteFamilyMaximal G F x = 0 := by
  by_cases h : G.Nonempty
  · rw [finiteFamilyMaximal, dite_eq_left h]
    apply Finset.sup'_eq_of_forall
    intro Q hQ
    exact Set.indicator_of_notMem
      (fun hxQ => hx (productBox_subset_root_of_mem_productDescendants (hG hQ) hxQ)) _
  · simp [finiteFamilyMaximal, h]

/-- The ordinary finite-family bound, with one factor for every coordinate. -/
theorem finite_family_maximal_integral
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hd : ∀ i, 0 < d i)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (p : ℝ) (hp : 1 < p) :
    (∫ x in productBox I, Real.rpow (finiteFamilyMaximal G F x) p) ≤
      Real.rpow (p / (p - 1)) (p * (m : ℝ)) *
        ∫ x in productBox I, Real.rpow |F.1 x| p := by
  have hM := productLeafConstant_finiteFamilyMaximal I N G hG F
  have hP := productLeafConstant_finiteProductMaximal I N Finset.univ F hf hs
  have hMI : IntegrableOn (fun x => Real.rpow (finiteFamilyMaximal G F x) p)
      (productBox I) volume := by
    apply integrableOn_productLeafConstant I N
    intro P hP x hx y hy
    dsimp only
    rw [hM P hP x hx y hy]
  have hPI : IntegrableOn
      (fun x => Real.rpow (finiteProductMaximal I N Finset.univ F x) p)
      (productBox I) volume := by
    apply integrableOn_productLeafConstant I N
    intro P hQ x hx y hy
    dsimp only
    rw [hP P hQ x hx y hy]
  calc
    _ ≤ ∫ x in productBox I, Real.rpow (finiteProductMaximal I N Finset.univ F x) p :=
      setIntegral_mono_on hMI hPI (measurableSet_productBox I) (fun x _ =>
        Real.rpow_le_rpow (finiteFamilyMaximal_nonneg G F x)
          (finiteFamilyMaximal_le_product I N G hG F x) (by linarith))
    _ ≤ _ := by
      simpa using finite_product_maximal_integral I N Finset.univ (fun i _ => hd i)
        F hf hs p hp

end ReyZygmund
