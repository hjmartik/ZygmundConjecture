import ReyZygmund.Geometry.FiniteSquare
import ReyZygmund.Geometry.ProductChildren
import ReyZygmund.Projection.FiniteIndices
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Allocation of nonzero product differences by square-function density

The density levels use the finite square function and product Lebesgue
measure. The nonzero child gives a strict lower tail, while boundedness of the
finite square function gives an upper tail. No last-level property is assumed.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem square_measurable
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) :
    Measurable (finiteSquareFunction I N Finset.univ F) := by
  exact Real.continuous_sqrt.measurable.comp
    (Finset.measurable_sum _ (fun Q _ =>
      (productDifferenceMap Finset.univ Q F).2.1.pow_const (2 : ℕ)))

private theorem square_bounded
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, finiteSquareFunction I N Finset.univ F x ≤ C := by
  choose C hC0 hC using fun Q : ∀ i, Box (Fin (d i)) =>
    (productDifferenceMap Finset.univ Q F).2.2
  refine ⟨Real.sqrt (∑ Q ∈ partialInterior I N Finset.univ, C Q ^ 2),
    Real.sqrt_nonneg _, ?_⟩
  intro x
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro Q _
  simpa only [sq_abs] using
    (sq_le_sq₀ (abs_nonneg ((productDifferenceMap Finset.univ Q F).1 x)) (hC0 Q)).mpr
      (hC Q x)

private theorem difference_abs_le_square
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (Q : ∀ i, Box (Fin (d i)))
    (hQ : Q ∈ Projection.productInterior I N) (x : ProductPoint d) :
    |(productDifferenceMap Finset.univ Q F).1 x| ≤
      finiteSquareFunction I N Finset.univ F x := by
  have hQ' : Q ∈ partialInterior I N Finset.univ := by
    apply Fintype.mem_piFinset.mpr
    intro i
    simpa only [Finset.mem_univ, ite_true] using Projection.mem_productInterior.mp hQ i
  have hterm : ((productDifferenceMap Finset.univ Q F).1 x) ^ 2 ≤
      ∑ P ∈ partialInterior I N Finset.univ,
        ((productDifferenceMap Finset.univ P F).1 x) ^ 2 :=
    Finset.single_le_sum (s := partialInterior I N Finset.univ)
      (f := fun P : ∀ i, Box (Fin (d i)) => ((productDifferenceMap Finset.univ P F).1 x) ^ 2)
      (a := Q) (fun _ _ => sq_nonneg _) hQ'
  exact Real.abs_le_sqrt hterm

private theorem product_interior_subset_root
    (I Q : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (hQ : Q ∈ Projection.productInterior I N) : productBox Q ⊆ productBox I := by
  intro x hx
  apply (mem_productBox I x).mpr
  intro i
  exact le_of_mem_descendants
    (interior_subset_descendants (I i) (N i) (Projection.mem_productInterior.mp hQ i))
    ((mem_productBox Q x).mp hx i)

private theorem product_volume_pos (Q : ∀ i, Box (Fin (d i))) :
    0 < volume.real (productBox Q) := by
  change 0 < (Measure.pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
    (Set.pi Set.univ (fun i => (Q i : Set (Fin (d i) → ℝ))))).toReal
  rw [Measure.pi_pi, ENNReal.toReal_prod]
  exact Finset.prod_pos (fun i _ => box_volume_pos (Q i))

private theorem product_volume_lt_top (Q : ∀ i, Box (Fin (d i))) :
    volume (productBox Q) < ∞ := by
  change Measure.pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
    (Set.pi Set.univ (fun i => (Q i : Set (Fin (d i) → ℝ)))) < ∞
  rw [Measure.pi_pi]
  exact ENNReal.prod_lt_top (fun i _ => (Q i).measure_coe_lt_top volume)

private theorem existsUnique_last_strict_level
    (a : ℤ → ℝ) (ha : Antitone a) (c : ℝ)
    (hnon : ∃ n, c < a n) (hbdd : ∃ b, ∀ n, c < a n → n ≤ b) :
    ∃! n : ℤ, c < a n ∧ a (n + 1) ≤ c := by
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd hbdd hnon
  refine ⟨n, ⟨hn, le_of_not_gt ?_⟩, ?_⟩
  · intro h
    have := hmax (n + 1) h
    omega
  · intro k hk
    apply le_antisymm (hmax k hk.1)
    by_contra h
    have hkn : k + 1 ≤ n := by omega
    have hle := ha hkn
    linarith [hk.2]

/-- Each nonzero full difference has a unique last strict square-density level, using
level sets restricted to the top rectangle. -/
theorem existsUnique_square_density_level
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (Q : ∀ i, Box (Fin (d i)))
    (hQ : Q ∈ Projection.productInterior I N)
    (hne : productDifferenceMap Finset.univ Q F ≠ 0) :
    let δ : ℝ := 1 / (2 : ℝ) ^ ((∑ i, d i) + 1)
    let Ω : ℤ → Set (ProductPoint d) := fun n =>
      {x | x ∈ productBox I ∧
        Real.rpow 2 (n : ℝ) < finiteSquareFunction I N Finset.univ F x}
    ∃! n : ℤ,
      δ * volume.real (productBox Q) < volume.real (productBox Q ∩ Ω n) ∧
        volume.real (productBox Q ∩ Ω (n + 1)) ≤ δ * volume.real (productBox Q) := by
  let δ : ℝ := 1 / (2 : ℝ) ^ ((∑ i, d i) + 1)
  let Ω : ℤ → Set (ProductPoint d) := fun n =>
    {x | x ∈ productBox I ∧
      Real.rpow 2 (n : ℝ) < finiteSquareFunction I N Finset.univ F x}
  change ∃! n : ℤ,
    δ * volume.real (productBox Q) < volume.real (productBox Q ∩ Ω n) ∧
      volume.real (productBox Q ∩ Ω (n + 1)) ≤ δ * volume.real (productBox Q)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hthreshold : 0 < δ * volume.real (productBox Q) :=
    mul_pos hδ (product_volume_pos Q)
  have hregular (n : ℤ) : MeasurableSet (productBox Q ∩ Ω n) ∧
      volume (productBox Q ∩ Ω n) < ∞ := by
    constructor
    · exact (measurableSet_productBox Q).inter
        ((measurableSet_productBox I).inter
          (measurableSet_lt measurable_const (square_measurable I N F)))
    · exact (measure_mono Set.inter_subset_left).trans_lt (product_volume_lt_top Q)
  have hmono : Antitone Ω := by
    intro a b hab x hx
    refine ⟨hx.1, ?_⟩
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (a : ℝ) ≤ (b : ℝ) by exact_mod_cast hab)).trans_lt hx.2
  have hdensity : Antitone (fun n : ℤ => volume.real (productBox Q ∩ Ω n)) := by
    intro a b hab
    exact measureReal_mono (fun _ hx => ⟨hx.1, hmono hab hx.2⟩) (hregular a).2.ne
  have hlow : ∃ n : ℤ,
      δ * volume.real (productBox Q) < volume.real (productBox Q ∩ Ω n) := by
    obtain ⟨R, hR, c, hc, hcR⟩ := productDifference_exists_nonzero_child Q F hne
    obtain ⟨k, hk⟩ := exists_mem_Ioc_zpow (abs_pos.mpr hc)
      (by norm_num : (1 : ℝ) < 2)
    have hk' : Real.rpow 2 (k : ℝ) < |c| := by
      simpa only [Real.rpow_eq_pow, Real.rpow_intCast] using hk.1
    have hRsub : productBox R ⊆ productBox Q ∩ Ω k := by
      intro x hx
      have hxQ := productLeaves_subset hR hx
      refine ⟨hxQ, product_interior_subset_root I Q N hQ hxQ, ?_⟩
      calc
        Real.rpow 2 (k : ℝ) < |c| := hk'
        _ = |(productDifferenceMap Finset.univ Q F).1 x| :=
          congrArg abs (hcR x hx).symm
        _ ≤ finiteSquareFunction I N Finset.univ F x :=
          difference_abs_le_square I N F Q hQ x
    have hRle := measureReal_mono hRsub (hregular k).2.ne
    have hchild : volume.real (productBox R) =
        2 * (δ * volume.real (productBox Q)) := by
      rw [product_child_volume Q R hR]
      dsimp only [δ]
      rw [pow_succ]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    refine ⟨k, ?_⟩
    rw [hchild] at hRle
    linarith
  have hhigh : ∃ b : ℤ, ∀ n : ℤ,
      δ * volume.real (productBox Q) < volume.real (productBox Q ∩ Ω n) → n ≤ b := by
    obtain ⟨C, hC0, hC⟩ := square_bounded I N F
    obtain ⟨b, hb⟩ := exists_mem_Ioc_zpow (show 0 < C + 1 by linarith)
      (by norm_num : (1 : ℝ) < 2)
    have hbhi : C < Real.rpow 2 ((b + 1 : ℤ) : ℝ) := by
      have h : C + 1 ≤ Real.rpow 2 ((b + 1 : ℤ) : ℝ) := by
        simpa only [Real.rpow_eq_pow, Real.rpow_intCast] using hb.2
      linarith
    refine ⟨b + 1, ?_⟩
    intro n hn
    by_contra h
    have hbn : b + 1 ≤ n := by omega
    have hrpow : Real.rpow 2 ((b + 1 : ℤ) : ℝ) ≤ Real.rpow 2 (n : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by exact_mod_cast hbn)
    have hempty : Ω n = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxS : Real.rpow 2 (n : ℝ) < finiteSquareFunction I N Finset.univ F x := hx.2
      linarith [hC x]
    rw [hempty, Set.inter_empty, measureReal_empty] at hn
    exact (not_lt_of_ge hthreshold.le) hn
  exact existsUnique_last_strict_level _ hdensity _ hlow hhigh

end ReyZygmund
