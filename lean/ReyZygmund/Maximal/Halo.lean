import ReyZygmund.Maximal.LevelSet

/-! # Density enlargement in a finite product grid

Apply the ordinary product maximal estimate to a measurable indicator. Constancy
on the smallest cubes permits use of the finite theorem. The improved incomparable
estimate is not used here.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- The indicator of a measurable set, as a bounded measurable function. -/
noncomputable def boundedIndicator (E : Set (ProductPoint d)) (hE : MeasurableSet E) :
    boundedMeasurableFunctions d :=
  ⟨E.indicator (fun _ => (1 : ℝ)), measurable_const.indicator hE, 1, by norm_num, by
    intro x
    by_cases hx : x ∈ E <;> simp [hx]⟩

private theorem indicator_square_integral
    (I : ∀ i, Box (Fin (d i))) (E : Set (ProductPoint d))
    (hE : MeasurableSet E) (hEI : E ⊆ productBox I) :
    (∫ x in productBox I, |(boundedIndicator E hE).1 x| ^ 2) = volume.real E := by
  have heq : (fun x => |(boundedIndicator E hE).1 x| ^ 2) =
      E.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ E <;> simp [boundedIndicator, hx]
  rw [heq, setIntegral_indicator hE, Set.inter_eq_right.mpr hEI, setIntegral_const]
  simp

/-- The ordinary finite maximal estimate gives the exact L2 halo cost. -/
theorem finite_root_halo_measure_le
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (E : Set (ProductPoint d)) (hE : MeasurableSet E) (hEI : E ⊆ productBox I)
    (hstep : ProductLeafConstant I N (E.indicator (fun _ => (1 : ℝ))))
    (δ : ℝ) (hδ : 0 < δ) :
    volume.real {x | x ∈ productBox I ∧
      δ < finiteFamilyMaximal (productDescendants I N) (boundedIndicator E hE) x} ≤
        (2 : ℝ) ^ (2 * m) / δ ^ 2 * volume.real E := by
  let F := boundedIndicator E hE
  let M := finiteFamilyMaximal (productDescendants I N) F
  have hs : ∀ x, x ∉ productBox I → F.1 x = 0 := by
    intro x hx
    exact Set.indicator_of_notMem (fun hxE => hx (hEI hxE)) (fun _ => (1 : ℝ))
  have hM := productLeafConstant_finiteFamilyMaximal I N (productDescendants I N)
    (fun _ h => h) F
  have hMi : IntegrableOn (fun x => (M x) ^ 2) (productBox I) volume := by
    apply integrableOn_productLeafConstant I N
    intro Q hQ x hx y hy
    dsimp only [M]
    rw [hM Q hQ x hx y hy]
  have hcheb := product_root_strict_level_le_square_integral I M hMi δ hδ
  have hmset : MeasurableSet {x | δ < M x} :=
    measurableSet_lt measurable_const (measurable_finiteFamilyMaximal _ F)
  rw [measureReal_restrict_apply hmset, Set.inter_comm] at hcheb
  have hmax := finite_family_maximal_integral I N (productDescendants I N)
    (fun _ h => h) hd F hstep hs 2 (by norm_num)
  have hmax' : (∫ x in productBox I, (M x) ^ 2) ≤
      (2 : ℝ) ^ (2 * m) * volume.real E := by
    have hpow : Real.rpow 2 ((2 : ℝ) * (m : ℝ)) = (2 : ℝ) ^ (2 * m) := by
      simp only [Real.rpow_eq_pow]
      rw [show (2 : ℝ) * (m : ℝ) = ((2 * m : ℕ) : ℝ) by push_cast; rfl,
        Real.rpow_natCast]
    simp only [Real.rpow_eq_pow, show (2 : ℝ) - 1 = 1 by norm_num,
      div_one, Real.rpow_two] at hmax
    change (∫ x in productBox I, (M x) ^ 2) ≤
      Real.rpow 2 (2 * (m : ℝ)) *
        (∫ x in productBox I, |(boundedIndicator E hE).1 x| ^ 2) at hmax
    rw [hpow, indicator_square_integral I E hE hEI] at hmax
    exact hmax
  exact hcheb.trans (by
    calc
      _ ≤ ((2 : ℝ) ^ (2 * m) * volume.real E) / δ ^ 2 :=
        div_le_div_of_nonneg_right hmax' (sq_nonneg δ)
      _ = _ := by ring)

/-- A rectangle exceeding the density threshold lies in the finite halo. -/
theorem productBox_subset_finite_root_halo
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (E : Set (ProductPoint d)) (hE : MeasurableSet E)
    (Q : ∀ i, Box (Fin (d i))) (hQ : Q ∈ productDescendants I N)
    (δ : ℝ) (hdensity : δ * volume.real (productBox Q) <
      volume.real (productBox Q ∩ E)) :
    productBox Q ⊆ {x | x ∈ productBox I ∧
      δ < finiteFamilyMaximal (productDescendants I N) (boundedIndicator E hE) x} := by
  have hvol : 0 < volume.real (productBox Q) := by
    change 0 < (Measure.pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
      (Set.pi Set.univ (fun i => (Q i : Set (Fin (d i) → ℝ))))).toReal
    rw [Measure.pi_pi, ENNReal.toReal_prod]
    exact Finset.prod_pos (fun i _ => box_volume_pos (Q i))
  have hi : (∫ y in productBox Q, |(boundedIndicator E hE).1 y|) =
      volume.real (productBox Q ∩ E) := by
    have heq : (fun y => |(boundedIndicator E hE).1 y|) =
        E.indicator (fun _ => (1 : ℝ)) := by
      funext y
      by_cases hy : y ∈ E <;> simp [boundedIndicator, hy]
    rw [heq, setIntegral_indicator hE, setIntegral_const]
    simp
  intro x hx
  refine ⟨productBox_subset_root_of_mem_productDescendants hQ hx, ?_⟩
  have hm := positiveMean_le_finiteFamilyMaximal (productDescendants I N)
    (boundedIndicator E hE) Q hQ x
  rw [Set.indicator_of_mem hx, hi] at hm
  exact ((lt_div_iff₀ hvol).mpr hdensity).trans_le hm

end ReyZygmund
