import ReyZygmund.Maximal.WeakerBound
import ReyZygmund.Maximal.GeneralInput

/-!
# General inputs under weaker containment

Section 6 of the paper reuses the Section 3 positive perturbation and smallest-cube
averaging reductions. Neither reduction requires incomparability: the weaker
finite positive estimate supplies the only changed geometric input.
Finite localization supplies all needed integrability. The coefficient-one
norm triangle inequality bounds the perturbation by its exact constant norm,
and an elementary real-order argument removes it without dividing by a norm.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

private theorem finiteFamilyMaximal_finiteInput_mono
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (f g : ProductPoint d → ℝ)
    (hf : ProductLeafConstant I N f) (hg : ProductLeafConstant I N g)
    (hfg : ∀ x ∈ productBox I, |f x| ≤ |g x|) (x : ProductPoint d) :
    finiteFamilyMaximal G (finiteInput I N f hf) x ≤
      finiteFamilyMaximal G (finiteInput I N g hg) x := by
  have hfi : IntegrableOn (fun y => |(finiteInput I N f hf).1 y|)
      (productBox I) volume := by
    simpa only [IntegrableOn, Real.norm_eq_abs] using
      (integrableOn_productLeafConstant I N (finiteInput I N f hf).1
        (productLeafConstant_indicator hf)).norm
  have hgi : IntegrableOn (fun y => |(finiteInput I N g hg).1 y|)
      (productBox I) volume := by
    simpa only [IntegrableOn, Real.norm_eq_abs] using
      (integrableOn_productLeafConstant I N (finiteInput I N g hg).1
        (productLeafConstant_indicator hg)).norm
  by_cases h : G.Nonempty
  · rw [finiteFamilyMaximal, dite_eq_left h]
    apply Finset.sup'_le
    intro Q hQ
    apply le_trans _ (positiveMean_le_finiteFamilyMaximal G
      (finiteInput I N g hg) Q hQ x)
    have hQI : productBox Q ⊆ productBox I :=
      productBox_subset_root_of_mem_productDescendants (hG hQ)
    have hi : (∫ y in productBox Q, |(finiteInput I N f hf).1 y|) ≤
        ∫ y in productBox Q, |(finiteInput I N g hg).1 y| := by
      apply setIntegral_mono_on (hfi.mono_set hQI) (hgi.mono_set hQI)
        (measurableSet_productBox Q)
      intro y hy
      change |(productBox I).indicator f y| ≤ |(productBox I).indicator g y|
      rw [Set.indicator_of_mem (hQI hy), Set.indicator_of_mem (hQI hy)]
      exact hfg y (hQI hy)
    by_cases hxQ : x ∈ productBox Q
    · rw [Set.indicator_of_mem hxQ, Set.indicator_of_mem hxQ]
      exact div_le_div_of_nonneg_right hi measureReal_nonneg
    · rw [Set.indicator_of_notMem hxQ, Set.indicator_of_notMem hxQ]
  · simp only [finiteFamilyMaximal, dite_eq_right h, le_refl]

private theorem root_norm_abs_of_nonneg
    (I : ∀ i, Box (Fin (d i))) (f : ProductPoint d → ℝ)
    (hf : ∀ x ∈ productBox I, 0 ≤ f x) (p : ℝ) :
    Real.rpow (∫ x in productBox I, Real.rpow |f x| p) (1 / p) =
      Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p) := by
  congr 1
  apply setIntegral_congr_fun (measurableSet_productBox I)
  intro x hx
  change Real.rpow |f x| p = Real.rpow (f x) p
  rw [abs_of_nonneg (hf x hx)]

private theorem root_norm_constant
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (ε : ℝ) (hε : 0 ≤ ε) (p : ℝ) (hp : 0 < p) :
    Real.rpow (∫ _x in productBox I, Real.rpow |ε| p) (1 / p) =
      ε * Real.rpow (volume.real (productBox I)) (1 / p) := by
  have h := rootLp_const_mul I N (fun _ => (1 : ℝ))
    (by intro Q hQ x hx y hy; rfl) ε p hp
  simpa only [Real.rpow_eq_pow, mul_one, abs_of_nonneg hε, abs_one, Real.one_rpow,
    setIntegral_const, smul_eq_mul] using h

private theorem le_of_positive_perturbations (a b c : ℝ) (hc : 0 ≤ c)
    (h : ∀ ε : ℝ, 0 < ε → a ≤ b + ε * c) : a ≤ b := by
  by_contra hab
  have hgap : 0 < a - b := by linarith
  let ε : ℝ := (a - b) / (2 * (c + 1))
  have hε : 0 < ε := div_pos hgap (by positivity)
  have hεeq : ε * (2 * (c + 1)) = a - b := by
    dsimp only [ε]
    exact div_mul_cancel₀ _ (by positivity)
  have hb := h ε hε
  nlinarith [mul_nonneg hε.le hc]

/-- Source Section 3 positive approximation for the finite represented
estimate. Nonnegative input, including zero input, has the unchanged constant. -/
theorem finite_weaker_maximal_norm_nonneg
    (hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → ∃ i, R i = S i)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfnonneg : ∀ x ∈ productBox I, 0 ≤ f x)
    (p : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 : ℝ) / 2) :
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal G (finiteInput I N f hf) x) p) (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p) := by
  let X := Real.rpow (∫ x in productBox I,
    Real.rpow (finiteFamilyMaximal G (finiteInput I N f hf) x) p) (1 / p)
  let Y := Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p)
  let C := maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1)
  let B := Real.rpow (volume.real (productBox I)) (1 / p)
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hdim : 0 ≤ maximalDimensionConstant d := by
    unfold maximalDimensionConstant
    exact sq_nonneg _
  have hC : 0 ≤ C := mul_nonneg hdim
    (pow_nonneg (div_nonneg hp0.le (sub_pos.mpr hp).le) _)
  have hB : 0 ≤ B := Real.rpow_nonneg measureReal_nonneg _
  change X ≤ C * Y
  apply le_of_positive_perturbations X (C * Y) (C * B) (mul_nonneg hC hB)
  intro ε hε
  let g : ProductPoint d → ℝ := fun x => f x + ε
  have hg : ProductLeafConstant I N g := by
    intro Q hQ x hx y hy
    exact congrArg (fun v => v + ε) (hf Q hQ x hx y hy)
  have hgpos : ∀ x ∈ productBox I, 0 < g x := by
    intro x hx
    exact add_pos_of_nonneg_of_pos (hfnonneg x hx) hε
  have hmono := rootLp_mono I N
    (finiteFamilyMaximal G (finiteInput I N f hf))
    (finiteFamilyMaximal G (finiteInput I N g hg))
    (productLeafConstant_finiteFamilyMaximal I N G hG _)
    (productLeafConstant_finiteFamilyMaximal I N G hG _)
    (fun x _ => by
      rw [abs_of_nonneg (finiteFamilyMaximal_nonneg _ _ _),
        abs_of_nonneg (finiteFamilyMaximal_nonneg _ _ _)]
      apply finiteFamilyMaximal_finiteInput_mono I N G hG f g hf hg _ x
      intro y hy
      rw [abs_of_nonneg (hfnonneg y hy), abs_of_nonneg (hgpos y hy).le]
      exact le_add_of_nonneg_right hε.le) p hp0
  have hmono' : X ≤ Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal G (finiteInput I N g hg) x) p) (1 / p) := by
    simpa only [X, abs_of_nonneg (finiteFamilyMaximal_nonneg _ _ _)] using hmono
  have hstrict := finite_weaker_maximal_norm hm I N hd G hG hweak
    g hg hgpos p hp hp3
  have htri := rootLp_add_le I N f (fun _ => ε) hf
    (by intro Q hQ x hx y hy; rfl) p hp.le
  change Real.rpow (∫ x in productBox I, Real.rpow |g x| p) (1 / p) ≤
    Real.rpow (∫ x in productBox I, Real.rpow |f x| p) (1 / p) +
      Real.rpow (∫ _x in productBox I, Real.rpow |ε| p) (1 / p) at htri
  have hga := root_norm_abs_of_nonneg I g (fun x hx => (hgpos x hx).le) p
  have hfa := root_norm_abs_of_nonneg I f hfnonneg p
  rw [hga, hfa, root_norm_constant I N ε hε.le p hp0] at htri
  calc
    X ≤ Real.rpow (∫ x in productBox I,
        Real.rpow (finiteFamilyMaximal G (finiteInput I N g hg) x) p) (1 / p) := hmono'
    _ ≤ C * Real.rpow (∫ x in productBox I, Real.rpow (g x) p) (1 / p) := hstrict
    _ ≤ C * (Y + ε * B) := mul_le_mul_of_nonneg_left htri hC
    _ = C * Y + ε * (C * B) := by ring

/-- The finite weaker-containment estimate assumes integrability of the input and its
absolute p-th power on the top rectangle. The dimension-only factor is uniform in
the smallest scale, top rectangle, family, input and real exponent p > 1. -/
theorem finite_weaker_general_input_norm
    (hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hweak : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → ∃ i, R i = S i)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : IntegrableOn f (productBox I) volume)
    (hpow : IntegrableOn (fun x => Real.rpow |f x| p) (productBox I) volume) :
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFunctionMaximal G f x) p) (1 / p) ≤
      (maximalDimensionConstant d + 3) * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow |f x| p) (1 / p) := by
  let g := leafAverage I N (fun x => |f x|)
  have hg : ProductLeafConstant I N g := productLeafConstant_leafAverage I N _
  have hnonneg : ∀ x, 0 ≤ g x :=
    leafAverage_nonneg I N (fun x => |f x|) (fun x _ => abs_nonneg (f x))
  let F := finiteInput I N g hg
  have hF : ProductLeafConstant I N F.1 := productLeafConstant_indicator hg
  have hs : ∀ x, x ∉ productBox I → F.1 x = 0 :=
    fun x hx => Set.indicator_of_notMem hx g
  have hpower : (∫ x in productBox I, Real.rpow (g x) p) ≤
      ∫ x in productBox I, Real.rpow |f x| p := by
    have h := integral_abs_rpow_leafAverage_le I N (fun x => |f x|) p hp.le hf.abs
      (by simpa only [abs_abs] using hpow)
    simpa only [g, abs_abs, abs_of_nonneg (hnonneg _)] using h
  have hnorm : Real.rpow (∫ x in productBox I, Real.rpow (g x) p) (1 / p) ≤
      Real.rpow (∫ x in productBox I, Real.rpow |f x| p) (1 / p) :=
    Real.rpow_le_rpow (integral_nonneg (fun x => Real.rpow_nonneg (hnonneg x) p))
      hpower (one_div_nonneg.mpr (zero_lt_one.trans hp).le)
  have hK : 0 ≤ maximalDimensionConstant d := by
    unfold maximalDimensionConstant
    exact sq_nonneg _
  have hC : 0 ≤ (p / (p - 1)) ^ (m - 1) :=
    pow_nonneg (div_nonneg (zero_lt_one.trans hp).le (sub_pos.mpr hp).le) _
  have hY : 0 ≤ Real.rpow (∫ x in productBox I, Real.rpow (g x) p) (1 / p) :=
    Real.rpow_nonneg (integral_nonneg (fun x => Real.rpow_nonneg (hnonneg x) p)) _
  rw [finiteFunctionMaximal_leafAverage I N G hG f hf]
  have hfinite : Real.rpow (∫ x in productBox I,
      Real.rpow (finiteFamilyMaximal G F x) p) (1 / p) ≤
      (maximalDimensionConstant d + 3) * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow (g x) p) (1 / p) := by
    by_cases hp3 : p ≤ (3 : ℝ) / 2
    · exact (finite_weaker_maximal_norm_nonneg hm I N hd G hG hweak
        g hg (fun x _ => hnonneg x) p hp hp3).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num)) hC) hY)
    · have hu := finite_family_maximal_norm_upper (by omega) I N G hG hd F hF hs
        p (le_of_not_ge hp3)
      have hFu : (∫ x in productBox I, Real.rpow |F.1 x| p) =
          ∫ x in productBox I, Real.rpow (g x) p := by
        apply setIntegral_congr_fun (measurableSet_productBox I)
        intro x hx
        change Real.rpow |(productBox I).indicator g x| p = Real.rpow (g x) p
        rw [Set.indicator_of_mem hx, abs_of_nonneg (hnonneg x)]
      rw [hFu] at hu
      exact hu.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK) hC) hY)
  exact hfinite.trans (mul_le_mul_of_nonneg_left hnorm
    (mul_nonneg (add_nonneg hK (by norm_num)) hC))

end ReyZygmund

