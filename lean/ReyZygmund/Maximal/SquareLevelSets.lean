import ReyZygmund.Maximal.Halo
import ReyZygmund.Maximal.SquareLevels

/-! # Square-function level sets and their enlargements

The finite square function defines the sets used for density grouping. Its
properties give their measurability, nesting and constancy of the indicators on
the smallest cubes.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

def finiteSquareLevelSet
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (n : ℤ) : Set (ProductPoint d) :=
  {x | x ∈ productBox I ∧ Real.rpow 2 (n : ℝ) < finiteSquareFunction I N Finset.univ F x}

theorem measurableSet_finiteSquareLevelSet
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (n : ℤ) :
    MeasurableSet (finiteSquareLevelSet I N F n) := by
  have hS : Measurable (finiteSquareFunction I N Finset.univ F) :=
    Real.continuous_sqrt.measurable.comp
    (Finset.measurable_sum _ (fun Q _ =>
      (productDifferenceMap Finset.univ Q F).2.1.pow_const (2 : ℕ)))
  exact (measurableSet_productBox I).inter (measurableSet_lt measurable_const hS)

theorem finiteSquareLevelSet_antitone
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) : Antitone (finiteSquareLevelSet I N F) := by
  intro a b hab x hx
  refine ⟨hx.1, ?_⟩
  exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (by exact_mod_cast hab)).trans_lt hx.2

theorem productLeafConstant_squareLevel_indicator
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) (n : ℤ) :
    ProductLeafConstant I N
      ((finiteSquareLevelSet I N F n).indicator (fun _ => (1 : ℝ))) := by
  intro Q hQ x hx y hy
  have hxy := productLeafConstant_finiteSquareFunction I N Finset.univ F hf hs
    Q hQ x hx y hy
  have hmem : x ∈ finiteSquareLevelSet I N F n ↔
      y ∈ finiteSquareLevelSet I N F n := by
    simp only [finiteSquareLevelSet, Set.mem_ofPred_eq, productLeaves_subset hQ hx,
      productLeaves_subset hQ hy, true_and, hxy]
  by_cases hxE : x ∈ finiteSquareLevelSet I N F n
  · rw [Set.indicator_of_mem hxE, Set.indicator_of_mem (hmem.mp hxE)]
  · rw [Set.indicator_of_notMem hxE, Set.indicator_of_notMem (mt hmem.mpr hxE)]

def finiteSquareHalo
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (n : ℤ) : Set (ProductPoint d) :=
  {x | x ∈ productBox I ∧ 1 / (2 : ℝ) ^ ((∑ i, d i) + 1) <
    finiteFamilyMaximal (productDescendants I N)
      (boundedIndicator (finiteSquareLevelSet I N F n)
        (measurableSet_finiteSquareLevelSet I N F n)) x}

theorem measurableSet_finiteSquareHalo
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (n : ℤ) :
    MeasurableSet (finiteSquareHalo I N F n) :=
  (measurableSet_productBox I).inter
    (measurableSet_lt measurable_const (measurable_finiteFamilyMaximal _ _))

/-- The exact dimension/cube-count cost before the paper's coarse simplification. -/
theorem finiteSquareHalo_measure_le
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) (n : ℤ) :
    volume.real (finiteSquareHalo I N F n) ≤
      (2 : ℝ) ^ (2 * m) / (1 / (2 : ℝ) ^ ((∑ i, d i) + 1)) ^ 2 *
        volume.real (finiteSquareLevelSet I N F n) :=
  finite_root_halo_measure_le I N hd _ (measurableSet_finiteSquareLevelSet I N F n)
    (fun _ hx => hx.1) (productLeafConstant_squareLevel_indicator I N F hf hs n)
    _ (by positivity)

private theorem indicator_mean
    (Q : ∀ i, Box (Fin (d i))) (E : Set (ProductPoint d)) (hE : MeasurableSet E) :
    (∫ y in productBox Q, |(boundedIndicator E hE).1 y|) =
      volume.real (productBox Q ∩ E) := by
  have heq : (fun y => |(boundedIndicator E hE).1 y|) =
      E.indicator (fun _ => (1 : ℝ)) := by
    funext y
    by_cases hy : y ∈ E <;> simp [boundedIndicator, hy]
  rw [heq, setIntegral_indicator hE, setIntegral_const]
  simp

private theorem finite_family_indicator_mono
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (E B : Set (ProductPoint d)) (hE : MeasurableSet E) (hB : MeasurableSet B)
    (hEB : E ⊆ B) (x : ProductPoint d) :
    finiteFamilyMaximal (productDescendants I N) (boundedIndicator E hE) x ≤
      finiteFamilyMaximal (productDescendants I N) (boundedIndicator B hB) x := by
  rw [finiteFamilyMaximal, dite_eq_left ⟨I, root_mem_productDescendants I N⟩]
  apply Finset.sup'_le
  intro Q hQ
  apply le_trans _ (positiveMean_le_finiteFamilyMaximal _ (boundedIndicator B hB) Q hQ x)
  by_cases hxQ : x ∈ productBox Q
  · rw [Set.indicator_of_mem hxQ, Set.indicator_of_mem hxQ,
      indicator_mean Q E hE, indicator_mean Q B hB]
    apply div_le_div_of_nonneg_right _ measureReal_nonneg
    have hvol : volume (productBox Q) < ∞ := by
      change Measure.pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
        (Set.pi Set.univ (fun i => (Q i : Set (Fin (d i) → ℝ)))) < ∞
      rw [Measure.pi_pi]
      exact ENNReal.prod_lt_top (fun i _ => (Q i).measure_coe_lt_top volume)
    exact measureReal_mono (Set.inter_subset_inter_right _ hEB)
      ((measure_mono Set.inter_subset_left).trans_lt hvol).ne
  · rw [Set.indicator_of_notMem hxQ, Set.indicator_of_notMem hxQ]

theorem finiteSquareHalo_antitone
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) : Antitone (finiteSquareHalo I N F) := by
  intro a b hab x hx
  refine ⟨hx.1, hx.2.trans_le ?_⟩
  exact finite_family_indicator_mono I N _ _
    (measurableSet_finiteSquareLevelSet I N F b)
    (measurableSet_finiteSquareLevelSet I N F a)
    (finiteSquareLevelSet_antitone I N F hab) x

end ReyZygmund
