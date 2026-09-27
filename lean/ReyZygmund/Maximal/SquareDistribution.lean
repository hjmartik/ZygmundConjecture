import ReyZygmund.Maximal.DensityPiece
import ReyZygmund.Maximal.GroupedEnergy
import ReyZygmund.Maximal.LayerCakeIntegral

/-! # The signed maximal distribution estimate

Upper density groups cancel outside their enlargement. Chebyshev's inequality and
the ordinary product maximal estimate control the lower groups using their energy
bounds. The resulting distribution inequality is used in the layer-cake argument.


-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

private theorem distribution_root_finite (I : ∀ i, Box (Fin (d i))) :
    volume (productBox I) ≠ ∞ := by
  change Measure.pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
    (Set.pi Set.univ (fun i => (I i : Set (Fin (d i) → ℝ)))) ≠ ∞
  rw [Measure.pi_pi]
  exact (ENNReal.prod_lt_top (fun i _ => (I i).measure_coe_lt_top volume)).ne

/-- Finite sums of interior differences retain the localized input class. -/
theorem productDifference_sum_productStep_closure
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (H : Finset (∀ i, Box (Fin (d i)))) (hH : H ⊆ productInterior I N) :
    ProductLeafConstant I N (∑ Q ∈ H, productDifferenceMap Finset.univ Q F).1 ∧
      ∀ x, x ∉ productBox I →
        (∑ Q ∈ H, productDifferenceMap Finset.univ Q F).1 x = 0 := by
  have hc Q (hQ : Q ∈ H) := productDifferenceMap_productStep_closure I N F hf hs
    Finset.univ Q (fun i _ => mem_productInterior.mp (hH hQ) i)
  constructor
  · simpa only [Submodule.coe_sum] using productLeafConstant_finsetSum H
      (fun Q => (productDifferenceMap Finset.univ Q F).1) (fun Q hQ => (hc Q hQ).1)
  · intro x hx
    simp only [Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_eq_zero (fun Q hQ => (hc Q hQ).2 x hx)

/-- The strict weighted tail is summable, even though the density
indices range over all integers. -/
theorem summable_square_level_tail
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) (n : ℤ) :
    Summable (fun j : ℤ => if j < n then Real.rpow 2 (2 * (j : ℝ)) *
      volume.real (finiteSquareLevelSet I N F j) else 0) := by
  have ht := summable_dyadic_layerCake_integral I N
    (finiteSquareFunction I N Finset.univ F)
    (productLeafConstant_finiteSquareFunction I N Finset.univ F hf hs)
    (fun _ _ => Real.sqrt_nonneg _) 2 (by norm_num)
  apply Summable.of_nonneg_of_le _ _ ht
  · intro j
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) measureReal_nonneg
    · exact le_rfl
  · intro j
    split_ifs
    · rfl
    · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) measureReal_nonneg

/-- The finite counterpart of the paper's distribution estimate, with exactly
the dimensional coefficient used before layer cake. -/
theorem finite_square_distribution
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) (n : ℤ) :
    volume.real {x | x ∈ productBox I ∧ Real.rpow 2 (n : ℝ) <
      finiteSignedProductMaximal I N
        (∑ Q ∈ productInterior I N, productDifferenceMap Finset.univ Q F) x} ≤
      (2 : ℝ) ^ (6 * (∑ i, d i) + 5) *
        (volume.real (finiteSquareLevelSet I N F n) + Real.rpow 2 (-2 * (n : ℝ)) *
          ∑' j : ℤ, if j < n then Real.rpow 2 (2 * (j : ℝ)) *
            volume.real (finiteSquareLevelSet I N F j) else 0) := by
  let L := ∑ Q ∈ squareLowerIndices I N F n, productDifferenceMap Finset.univ Q F
  let G := ∑ Q ∈ productInterior I N, productDifferenceMap Finset.univ Q F
  let M := finiteFamilyMaximal (productDescendants I N) L
  let E := {x | x ∈ productBox I ∧ Real.rpow 2 (n : ℝ) < M x}
  let tail := ∑' j : ℤ, if j < n then Real.rpow 2 (2 * (j : ℝ)) *
    volume.real (finiteSquareLevelSet I N F j) else 0
  have htail : 0 ≤ tail := tsum_nonneg (fun j => by
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) measureReal_nonneg
    · exact le_rfl)
  have hH : squareLowerIndices I N F n ⊆ productInterior I N := by
    intro Q hQ
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hQ).1).1
  have hL := productDifference_sum_productStep_closure I N F hf hs (squareLowerIndices I N F n) hH
  have hM := productLeafConstant_finiteFamilyMaximal I N (productDescendants I N)
    (fun _ h => h) L
  have hMi : IntegrableOn (fun x => (M x) ^ 2) (productBox I) volume := by
    apply integrableOn_productLeafConstant I N
    intro Q hQ x hx y hy
    exact congrArg (fun z : ℝ => z ^ 2) (hM Q hQ x hx y hy)
  have hlo : (∫ x in productBox I, (L.1 x) ^ 2) ≤
      (2 : ℝ) ^ (4 * (∑ i, d i) + 5) * tail := by
    simpa only [L, Submodule.coe_sum, Finset.sum_apply, tail] using
      squareLower_energy_le_tsum I N hd F n
        ((2 : ℝ) ^ (4 * (∑ i, d i) + 5)) (by positivity)
        (fun j => Real.rpow 2 (2 * (j : ℝ)) * volume.real (finiteSquareLevelSet I N F j))
        (fun _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _) measureReal_nonneg)
        (summable_square_level_tail I N F hf hs n)
        (fun j _ => by simpa only [mul_assoc] using finite_square_piece_energy I N hd F hf hs j)
  have hordinary := finite_family_maximal_integral I N (productDescendants I N)
    (fun _ h => h) hd L hL.1 hL.2 2 (by norm_num)
  have hpow : Real.rpow 2 ((2 : ℝ) * (m : ℝ)) = (2 : ℝ) ^ (2 * m) := by
    simp only [Real.rpow_eq_pow]
    rw [show (2 : ℝ) * (m : ℝ) = ((2 * m : ℕ) : ℝ) by push_cast; rfl,
      Real.rpow_natCast]
  simp only [Real.rpow_eq_pow, show (2 : ℝ) - 1 = 1 by norm_num,
    div_one, Real.rpow_two, sq_abs] at hordinary
  change (∫ x in productBox I, (M x) ^ 2) ≤
    Real.rpow 2 (2 * (m : ℝ)) * (∫ x in productBox I, (L.1 x) ^ 2) at hordinary
  rw [hpow] at hordinary
  have hcheb := product_root_strict_level_le_square_integral I M hMi
    (Real.rpow 2 (n : ℝ)) (Real.rpow_pos_of_pos (by norm_num) _)
  rw [measureReal_restrict_apply
    (measurableSet_lt measurable_const (measurable_finiteFamilyMaximal _ L)), Set.inter_comm] at hcheb
  have hinv : (Real.rpow 2 (n : ℝ)) ^ 2 * Real.rpow 2 (-2 * (n : ℝ)) = 1 := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [show (n : ℝ) * (2 : ℕ) + -2 * (n : ℝ) = 0 by ring, Real.rpow_zero]
  have he : volume.real E ≤ (2 : ℝ) ^ (2 * m) *
      (2 : ℝ) ^ (4 * (∑ i, d i) + 5) * Real.rpow 2 (-2 * (n : ℝ)) * tail := by
    calc
      _ ≤ (∫ x in productBox I, (M x) ^ 2) / (Real.rpow 2 (n : ℝ)) ^ 2 := hcheb
      _ ≤ ((2 : ℝ) ^ (2 * m) * ((2 : ℝ) ^ (4 * (∑ i, d i) + 5) * tail)) /
          (Real.rpow 2 (n : ℝ)) ^ 2 :=
        div_le_div_of_nonneg_right
          (hordinary.trans (mul_le_mul_of_nonneg_left hlo (by positivity))) (sq_nonneg _)
      _ = _ := by
        apply (div_eq_iff (pow_ne_zero 2 (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne')).mpr
        calc
          _ = ((2 : ℝ) ^ (2 * m) * (2 : ℝ) ^ (4 * (∑ i, d i) + 5) * tail) *
              ((Real.rpow 2 (n : ℝ)) ^ 2 * Real.rpow 2 (-2 * (n : ℝ))) := by rw [hinv, mul_one]; ring
          _ = _ := by simp only [Real.rpow_eq_pow]; ring
  have hsubset : {x | x ∈ productBox I ∧ Real.rpow 2 (n : ℝ) <
      finiteSignedProductMaximal I N G x} ⊆ finiteSquareHalo I N F n ∪ E := by
    intro x hx
    by_cases hb : x ∈ finiteSquareHalo I N F n
    · exact Or.inl hb
    · apply Or.inr
      refine ⟨hx.1, ?_⟩
      have heq := signedMaximal_eq_lower_off_halo I N hd F n x hb
      change finiteSignedProductMaximal I N G x = finiteSignedProductMaximal I N L x at heq
      have hx' := hx.2
      rw [heq] at hx'
      exact hx'.trans_le (finiteSignedProductMaximal_le_positive I N L x)
  have hset : volume.real {x | x ∈ productBox I ∧ Real.rpow 2 (n : ℝ) <
      finiteSignedProductMaximal I N G x} ≤ volume.real (finiteSquareHalo I N F n) + volume.real E :=
    (measureReal_mono hsubset (measure_ne_top_of_subset
      (fun _ hx => hx.elim (fun h => h.1) (fun h => h.1)) (distribution_root_finite I))).trans
      (measureReal_union_le _ _)
  have hm := parameter_count_le_total_dimension hd
  have hhalo := finiteSquareHalo_measure_le I N hd F hf hs n
  have hhaloC : (2 : ℝ) ^ (2 * m) / (1 / (2 : ℝ) ^ ((∑ i, d i) + 1)) ^ 2 ≤
      (2 : ℝ) ^ (6 * (∑ i, d i) + 5) := by
    have heq : (2 : ℝ) ^ (2 * m) / (1 / (2 : ℝ) ^ ((∑ i, d i) + 1)) ^ 2 =
        (2 : ℝ) ^ (2 * m + 2 * (∑ i, d i) + 2) := by
      simp only [div_pow, one_pow, div_div_eq_mul_div, div_one, ← pow_mul, ← pow_add]
      congr 1
      omega
    rw [heq]
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    omega
  have henergyC : (2 : ℝ) ^ (2 * m) * (2 : ℝ) ^ (4 * (∑ i, d i) + 5) ≤
      (2 : ℝ) ^ (6 * (∑ i, d i) + 5) := by
    rw [← pow_add]
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    omega
  calc
    _ ≤ volume.real (finiteSquareHalo I N F n) + volume.real E := hset
    _ ≤ (2 : ℝ) ^ (6 * (∑ i, d i) + 5) * volume.real (finiteSquareLevelSet I N F n) +
        (2 : ℝ) ^ (6 * (∑ i, d i) + 5) * Real.rpow 2 (-2 * (n : ℝ)) * tail := by
      apply add_le_add
      · exact hhalo.trans (mul_le_mul_of_nonneg_right hhaloC measureReal_nonneg)
      · exact he.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right henergyC (Real.rpow_nonneg (by norm_num) _)) htail)
    _ = _ := by ring

end ReyZygmund
