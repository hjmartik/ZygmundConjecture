import ReyZygmund.Maximal.SquareGrouping
import ReyZygmund.Maximal.PieceEnergy

/-!
# The energy of the density groups

The density index supplies the small-set hypothesis, and its halo contains
every parent in the group. The paper's coefficient is obtained from the
halo estimate and the positive coordinate dimensions.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- The dimension inequality used to coarsen the exact product maximal cost. -/
theorem parameter_count_le_total_dimension (hd : ∀ i, 0 < d i) :
    m ≤ ∑ i, d i := by
  calc
    m = ∑ _i : Fin m, 1 := by simp
    _ ≤ ∑ i, d i := Finset.sum_le_sum (fun i _ => hd i)

private theorem halo_coefficient_identity :
    (2 : ℝ) ^ (2 * m) / (1 / (2 : ℝ) ^ ((∑ i, d i) + 1)) ^ 2 =
      (2 : ℝ) ^ (2 * m + 2 * (∑ i, d i) + 2) := by
  simp only [div_pow, one_pow, div_div_eq_mul_div, div_one, ← pow_mul, ← pow_add]
  congr 1
  omega

/-- Each density group has the paper's precise coarse dimensional energy
bound; the estimate does not assume the energy or halo conclusion. -/
theorem finite_square_piece_energy
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) (n : ℤ) :
    (∫ x in productBox I,
      (∑ Q ∈ squarePieceIndices I N F n, (productDifferenceMap Finset.univ Q F).1 x) ^ 2) ≤
      (2 : ℝ) ^ (4 * (∑ i, d i) + 5) * Real.rpow 2 (2 * (n : ℝ)) *
        volume.real (finiteSquareLevelSet I N F n) := by
  have hH : squarePieceIndices I N F n ⊆ productInterior I N := by
    intro Q hQ
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hQ).1).1
  have hcover : ∀ Q ∈ squarePieceIndices I N F n,
      productBox Q ⊆ finiteSquareHalo I N F n := by
    intro Q hQ
    obtain ⟨hQ0, hj⟩ := Finset.mem_filter.mp hQ
    simpa only [hj] using productBox_subset_squareDensityHalo I N F Q hQ0
  have hden : ∀ Q ∈ squarePieceIndices I N F n,
      volume.real (productBox Q ∩ finiteSquareLevelSet I N F (n + 1)) ≤
        (1 / (2 : ℝ) ^ ((∑ i, d i) + 1)) * volume.real (productBox Q) := by
    intro Q hQ
    obtain ⟨hQ0, hj⟩ := Finset.mem_filter.mp hQ
    simpa only [hj] using (squareDensityIndex_spec I N F Q hQ0).2
  have hbound : ∀ x ∈ finiteSquareHalo I N F n \ finiteSquareLevelSet I N F (n + 1),
      finiteSquareFunction I N Finset.univ F x ≤ Real.rpow 2 ((n + 1 : ℤ) : ℝ) := by
    intro x hx
    exact le_of_not_gt (fun h => hx.2 ⟨hx.1.1, h⟩)
  have he := finite_piece_energy I N hd F (squarePieceIndices I N F n) hH
    (finiteSquareLevelSet I N F (n + 1)) (finiteSquareHalo I N F n)
    (measurableSet_finiteSquareLevelSet I N F _) (measurableSet_finiteSquareHalo I N F _)
    (fun _ hx => hx.1) hcover hden (Real.rpow 2 ((n + 1 : ℤ) : ℝ))
    (Real.rpow_nonneg (by norm_num) _) hbound
  have hh := finiteSquareHalo_measure_le I N hd F hf hs n
  rw [halo_coefficient_identity] at hh
  have hshift : Real.rpow 2 ((n + 1 : ℤ) : ℝ) = Real.rpow 2 (n : ℝ) * 2 := by
    simp only [Real.rpow_eq_pow]
    rw [Int.cast_add, Int.cast_one, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_one]
  have hsq : (Real.rpow 2 (n : ℝ)) ^ 2 = Real.rpow 2 (2 * (n : ℝ)) := by
    simp only [Real.rpow_eq_pow]
    rw [show 2 * (n : ℝ) = (n : ℝ) * (2 : ℕ) by ring,
      Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  have hscale :
      2 * (Real.rpow 2 ((n + 1 : ℤ) : ℝ)) ^ 2 *
        (2 : ℝ) ^ (2 * m + 2 * (∑ i, d i) + 2) =
      (2 : ℝ) ^ (2 * m + 2 * (∑ i, d i) + 5) * Real.rpow 2 (2 * (n : ℝ)) := by
    rw [hshift, mul_pow, hsq,
      show 2 * m + 2 * (∑ i, d i) + 5 = (2 * m + 2 * (∑ i, d i) + 2) + 3 by omega,
      pow_add]
    norm_num
    ring
  have hc : (2 : ℝ) ^ (2 * m + 2 * (∑ i, d i) + 5) ≤
      (2 : ℝ) ^ (4 * (∑ i, d i) + 5) := by
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hm := parameter_count_le_total_dimension hd
    omega
  calc
    _ ≤ 2 * (Real.rpow 2 ((n + 1 : ℤ) : ℝ)) ^ 2 *
        volume.real (finiteSquareHalo I N F n) := he
    _ ≤ 2 * (Real.rpow 2 ((n + 1 : ℤ) : ℝ)) ^ 2 *
        ((2 : ℝ) ^ (2 * m + 2 * (∑ i, d i) + 2) *
          volume.real (finiteSquareLevelSet I N F n)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = (2 : ℝ) ^ (2 * m + 2 * (∑ i, d i) + 5) * Real.rpow 2 (2 * (n : ℝ)) *
        volume.real (finiteSquareLevelSet I N F n) := by rw [← mul_assoc, hscale]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by norm_num) _)) measureReal_nonneg

end ReyZygmund
