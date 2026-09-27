import ReyZygmund.Maximal.LayerCakeIntegral
import ReyZygmund.Maximal.GeometricConvolution

/-! # From distribution bounds to power-integral bounds

Assume the distribution inequality. The measures of level sets in the finite top
rectangle prove summability of the tails and convolution. The resulting
coefficient is `4 * (1 + 3) * 2 = 32`.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem dyadic_weight_split (p : ℝ) (n : ℤ) (s : ℝ) :
    Real.rpow 2 ((2 - p) * (n : ℝ)) * (Real.rpow 2 (p * (n : ℝ)) * s) =
      Real.rpow 2 (2 * (n : ℝ)) * s := by
  rw [← mul_assoc]
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    show (2 - p) * (n : ℝ) + p * (n : ℝ) = 2 * (n : ℝ) by ring]

private theorem dyadic_weight_shift (p : ℝ) (n : ℤ) :
    Real.rpow 2 (p * (n : ℝ)) * Real.rpow 2 (-2 * (n : ℝ)) =
      Real.rpow 2 ((p - 2) * (n : ℝ)) := by
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    show p * (n : ℝ) + -2 * (n : ℝ) = (p - 2) * (n : ℝ) by ring]

/-- The power-integral estimate on the top rectangle, conditional on the distribution
bound. Convergence is proved, and values outside the rectangle are unrestricted. -/
theorem integral_rpow_le_of_dyadic_distribution
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (H K : ProductPoint d → ℝ)
    (hH : ProductLeafConstant I N H) (hK : ProductLeafConstant I N K)
    (hH0 : ∀ x ∈ productBox I, 0 ≤ H x) (hK0 : ∀ x ∈ productBox I, 0 ≤ K x)
    (C : ℝ) (hC : 0 ≤ C)
    (hdistribution : ∀ n : ℤ,
      volume.real {x | x ∈ productBox I ∧ Real.rpow 2 (n : ℝ) < H x} ≤
        C * (volume.real {x | x ∈ productBox I ∧ Real.rpow 2 (n : ℝ) < K x} +
          Real.rpow 2 (-2 * (n : ℝ)) *
            ∑' j : ℤ, if j < n then Real.rpow 2 (2 * (j : ℝ)) *
              volume.real {x | x ∈ productBox I ∧ Real.rpow 2 (j : ℝ) < K x} else 0))
    (p : ℝ) (hp : 1 ≤ p) (hp3 : p ≤ (3 : ℝ) / 2) :
    (∫ x in productBox I, Real.rpow (H x) p) ≤
      32 * C * (∫ x in productBox I, Real.rpow (K x) p) := by
  let hLevels : ℤ → ℝ := fun n =>
    volume.real {x | x ∈ productBox I ∧ Real.rpow 2 (n : ℝ) < H x}
  let kLevels : ℤ → ℝ := fun n =>
    volume.real {x | x ∈ productBox I ∧ Real.rpow 2 (n : ℝ) < K x}
  let weightedH : ℤ → ℝ := fun n => Real.rpow 2 (p * (n : ℝ)) * hLevels n
  let weightedK : ℤ → ℝ := fun n => Real.rpow 2 (p * (n : ℝ)) * kLevels n
  let tail : ℤ → ℝ := fun n =>
    ∑' j : ℤ, if j < n then Real.rpow 2 (2 * (j : ℝ)) * kLevels j else 0
  let convolution : ℤ → ℝ := fun n =>
    ∑' j : ℕ, Real.rpow 2 ((p - 2) * ((j + 1 : ℕ) : ℝ)) *
      weightedK (n - ((j + 1 : ℕ) : ℤ))
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hsH : Summable weightedH :=
    summable_dyadic_layerCake_integral I N H hH hH0 p hp0
  have hsK : Summable weightedK :=
    summable_dyadic_layerCake_integral I N K hK hK0 p hp0
  have hweightedK (n : ℤ) : 0 ≤ weightedK n :=
    mul_nonneg (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
      measureReal_nonneg
  have hconv := geometric_convolution_sum p hp hp3 weightedK hweightedK hsK
  have hsConv : Summable convolution := hconv.1.summable
  have hconvle : (∑' n : ℤ, convolution n) ≤ 3 * (∑' n : ℤ, weightedK n) := hconv.2
  have hrow (n : ℤ) :
      Summable (fun j : ℤ => if j < n then Real.rpow 2 (2 * (j : ℝ)) * kLevels j else 0) ∧
        Real.rpow 2 ((p - 2) * (n : ℝ)) * tail n = convolution n := by
    obtain ⟨hs, heq⟩ :=
      geometric_convolution_strict_reindex p hp hp3 weightedK hweightedK hsK n
    have hterm (j : ℤ) :
        (if j < n then Real.rpow 2 ((2 - p) * (j : ℝ)) * weightedK j else 0) =
          (if j < n then Real.rpow 2 (2 * (j : ℝ)) * kLevels j else 0) := by
      by_cases hj : j < n
      · simp only [ite_eq_left hj]
        exact dyadic_weight_split p j (kLevels j)
      · simp only [ite_eq_right hj]
    refine ⟨hs.congr hterm, ?_⟩
    simpa only [hterm, tail, convolution] using heq
  have hpoint (n : ℤ) : weightedH n ≤ C * (weightedK n + convolution n) := by
    have hn := mul_le_mul_of_nonneg_left (hdistribution n)
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (p * (n : ℝ))).le
    change weightedH n ≤ Real.rpow 2 (p * (n : ℝ)) *
      (C * (kLevels n + Real.rpow 2 (-2 * (n : ℝ)) * tail n)) at hn
    calc
      weightedH n ≤ Real.rpow 2 (p * (n : ℝ)) *
          (C * (kLevels n + Real.rpow 2 (-2 * (n : ℝ)) * tail n)) := hn
      _ = C * (weightedK n + Real.rpow 2 ((p - 2) * (n : ℝ)) * tail n) := by
        dsimp only [weightedK]
        rw [← dyadic_weight_shift p n]
        ring
      _ = C * (weightedK n + convolution n) := by rw [(hrow n).2]
  have hsum : (∑' n : ℤ, weightedH n) ≤
      C * ((∑' n : ℤ, weightedK n) + ∑' n : ℤ, convolution n) := by
    calc
      _ ≤ ∑' n : ℤ, C * (weightedK n + convolution n) :=
        hsH.tsum_le_tsum hpoint ((hsK.add hsConv).mul_left C)
      _ = _ := by
        rw [(hsK.add hsConv).tsum_mul_left C, hsK.tsum_add hsConv]
  have hsum4 : (∑' n : ℤ, weightedH n) ≤ 4 * C * (∑' n : ℤ, weightedK n) := by
    calc
      _ ≤ C * ((∑' n : ℤ, weightedK n) + ∑' n : ℤ, convolution n) := hsum
      _ ≤ C * ((∑' n : ℤ, weightedK n) + 3 * (∑' n : ℤ, weightedK n)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hconvle) hC
      _ = _ := by ring
  have hHbound := (dyadic_layerCake_integral_bounds I N H hH hH0 p hp hp3).1
  have hKbound := (dyadic_layerCake_integral_bounds I N K hK hK0 p hp hp3).2
  change (∫ x in productBox I, Real.rpow (H x) p) / 4 ≤ ∑' n : ℤ, weightedH n at hHbound
  change (∑' n : ℤ, weightedK n) ≤ 2 * (∫ x in productBox I, Real.rpow (K x) p) at hKbound
  calc
    (∫ x in productBox I, Real.rpow (H x) p) ≤ 4 * (∑' n : ℤ, weightedH n) := by linarith
    _ ≤ 16 * C * (∑' n : ℤ, weightedK n) := by linarith [hsum4]
    _ ≤ 16 * C * (2 * (∫ x in productBox I, Real.rpow (K x) p)) :=
      mul_le_mul_of_nonneg_left hKbound (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hC)
    _ = 32 * C * (∫ x in productBox I, Real.rpow (K x) p) := by ring

end ReyZygmund
