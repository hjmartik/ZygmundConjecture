import ReyZygmund.Maximal.Coordinate
import ReyZygmund.Geometry.ProductIntegration

/-! # A coordinate maximal estimate on the top rectangle

Apply the one-coordinate maximal inequality to slices, then integrate over the
other factors of the top rectangle. Constancy on the smallest cubes gives the
required integrability. The input may be signed and is unrestricted outside the
top rectangle; the coefficient has no dimensional or volume factor.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem integral_bound_of_root_bound {A B C p : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hp : 0 < p)
    (h : A ^ (1 / p) ≤ C * B ^ (1 / p)) : A ≤ C ^ p * B := by
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hA _) h hp.le
  simpa only [one_div, Real.mul_rpow hC (Real.rpow_nonneg hB _),
    Real.rpow_inv_rpow hA hp.ne', Real.rpow_inv_rpow hB hp.ne'] using hpow

/-- Express the norm inequality in integral form. -/
private theorem finite_maximal_integral_bound (k : ℕ) (hk : 0 < k)
    (J : Box (Fin k)) (n : ℕ) (g : (Fin k → ℝ) → ℝ)
    (p : ℝ) (hp : 1 < p)
    (hg : ∀ Q ∈ leaves J n, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y) :
    (∫ x in (J : Set (Fin k → ℝ)), finiteDyadicMaximal J n g x ^ p) ≤
      (p / (p - 1)) ^ p * (∫ x in (J : Set (Fin k → ℝ)), |g x| ^ p) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  apply integral_bound_of_root_bound
    (integral_nonneg (fun x =>
      Real.rpow_nonneg (finiteDyadicMaximal_nonneg J n g x) p))
    (integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg (g x)) p))
    (div_nonneg hp0.le (sub_pos.mpr hp).le) hp0
  exact finite_dyadic_maximal_lp k hk J n g p hp hg

/-- Fixing the other coordinates at a point of the top rectangle gives a slice constant on the smallest cubes. -/
private theorem root_slice_leafConstant
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (j : Fin m) (x : ProductPoint d) (hx : x ∈ productBox I) :
    ∀ Q ∈ leaves (I j) (N j), ∀ y ∈ Q, ∀ z ∈ Q,
      f (Function.update x j y) = f (Function.update x j z) := by
  intro Q hQ y hy z hz
  have hmem (w : Fin (d j) → ℝ) (hw : w ∈ Q) :
      Function.update x j w ∈ productBox I := by
    apply (mem_productBox I _).mpr
    intro i
    by_cases hij : i = j
    · subst i
      simpa using (level (I j) (N j)).le_of_mem hQ hw
    · simpa [hij] using (mem_productBox I x).mp hx i
  simpa only [Set.indicator_of_mem (hmem y hy), Set.indicator_of_mem (hmem z hz)] using
    productStep_coordinate_leafConstant I N f hf j x Q hQ y hy z hz

/-- The finite coordinate maximal estimate with the exact source factor for
every real `p > 1`. No hypothesis is imposed outside the top rectangle. -/
theorem finite_coordinate_maximal_integral
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (j : Fin m) (hd : 0 < d j)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (p : ℝ) (hp : 1 < p) :
    (∫ x in productBox I, Real.rpow (coordinateDyadicMaximal j (I j) (N j) f x) p) ≤
      Real.rpow (p / (p - 1)) p * (∫ x in productBox I, Real.rpow |f x| p) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hM := productLeafConstant_coordinateDyadicMaximal hf j
  have hMp : ProductLeafConstant I N
      (fun x => Real.rpow (coordinateDyadicMaximal j (I j) (N j) f x) p) := by
    intro Q hQ x hx y hy
    exact congrArg (fun t : ℝ => Real.rpow t p) (hM Q hQ x hx y hy)
  have hfp : ProductLeafConstant I N (fun x => Real.rpow |f x| p) := by
    intro Q hQ x hx y hy
    exact congrArg (fun t : ℝ => Real.rpow |t| p) (hf Q hQ x hx y hy)
  refine integral_product_le_of_coordinate_le I N _ _ hMp hfp
    (fun x _ => Real.rpow_nonneg (coordinateDyadicMaximal_nonneg j (I j) (N j) f x) p)
    (fun x _ => Real.rpow_nonneg (abs_nonneg (f x)) p)
    _ (Real.rpow_nonneg (div_nonneg hp0.le (sub_pos.mpr hp).le) p) j ?_
  intro x hx
  change (∫ y in (I j : Set (Fin (d j) → ℝ)),
      coordinateDyadicMaximal j (I j) (N j) f (Function.update x j y) ^ p) ≤
    (p / (p - 1)) ^ p *
      (∫ y in (I j : Set (Fin (d j) → ℝ)), |f (Function.update x j y)| ^ p)
  simp_rw [coordinateDyadicMaximal_update]
  exact finite_maximal_integral_bound (d j) hd (I j) (N j)
    (fun y => f (Function.update x j y)) p hp (root_slice_leafConstant I N f hf j x hx)

end ReyZygmund
