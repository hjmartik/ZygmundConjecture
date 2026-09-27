import ReyZygmund.Geometry.SourceCutoff
import ReyZygmund.Maximal.GeneralInput
import ReyZygmund.Geometry.ProductLp

/-! # The finite estimate with a common smallest side length

The top rectangle and smallest side length are arbitrary. If that side length is
incompatible with a top cube, the original family is empty and the estimate
follows directly. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry Projection

theorem source_finite_incomparable_maximal_norm
    {m : ℕ} {d : Fin m → ℕ} (hm : 2 ≤ m) (hd : ∀ i, 0 < d i)
    (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubes (n i))
    (G : Finset (∀ i, Box (Fin (d i))))
    (hG : ∀ R ∈ G, R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
      ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → R = S)
    (f : ProductPoint d → ℝ) (hs : ∀ x, x ∉ productBox I → f x = 0)
    (hfpos : ∀ x ∈ productBox I, 0 < f x)
    (hf : ∀ R, (R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
      ∀ i u, (R i).upper u - (R i).lower u = (2 : ℝ) ^ (-k)) →
      ∀ x ∈ productBox R, ∀ y ∈ productBox R, f x = f y)
    (p : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 : ℝ) / 2) :
    Real.rpow (∫ x in productBox I, Real.rpow (finiteFunctionMaximal G f x) p) (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  obtain hnk | he := source_cutoff_or_empty hd D n k I hI G hG
  · let N := fun i => (k - n i).toNat
    have hfN : ProductLeafConstant I N f :=
      (source_productLeafConstant_iff hd D n k I hI hnk f).mpr hf
    have hGN : G ⊆ productDescendants I N := by
      intro R hR
      exact (source_productDescendants_iff hd D n k I hI hnk R).mpr (hG R hR)
    have hinput : (finiteInput I N f hfN).1 = f := by
      funext x
      by_cases hx : x ∈ productBox I
      · exact Set.indicator_of_mem hx f
      · change (productBox I).indicator f x = f x
        rw [Set.indicator_of_notMem hx, hs x hx]
    have h := finite_incomparable_maximal_norm hm I N hd G hGN
      (fun R hR S hS hRS => hinc R hR S hS ((productBox_subset_iff R S).mpr hRS))
      f hfN hfpos p hp hp3
    rw [← finiteFunctionMaximal_of_bounded G (finiteInput I N f hfN), hinput] at h
    exact h
  · subst G
    have hz : finiteFunctionMaximal (∅ : Finset (∀ i, Box (Fin (d i)))) f = 0 := by
      funext x
      simp only [finiteFunctionMaximal, Finset.not_nonempty_empty, dite_false, Pi.zero_apply]
    rw [hz]
    simp only [Pi.zero_apply, Real.rpow_eq_pow, Real.zero_rpow hp0.ne', integral_zero,
      Real.zero_rpow (one_div_ne_zero hp0.ne')]
    apply mul_nonneg
    · apply mul_nonneg
      · unfold maximalDimensionConstant
        positivity
      · exact pow_nonneg (div_nonneg hp0.le (sub_pos.mpr hp).le) _
    · apply Real.rpow_nonneg
      exact integral_nonneg_of_ae (ae_restrict_of_forall_mem (measurableSet_productBox I)
        (fun x hx => Real.rpow_nonneg (hfpos x hx).le p))

/-- The norm estimate includes the empty-family case forced by an incompatible
smallest scale. In the other case, constancy on the smallest cubes justifies
conversion from real power integrals. -/
theorem source_finite_incomparable_maximal_eLpNorm
    {m : ℕ} {d : Fin m → ℕ} (hm : 2 ≤ m) (hd : ∀ i, 0 < d i)
    (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubes (n i))
    (G : Finset (∀ i, Box (Fin (d i))))
    (hG : ∀ R ∈ G, R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
      ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → R = S)
    (f : ProductPoint d → ℝ) (hs : ∀ x, x ∉ productBox I → f x = 0)
    (hfpos : ∀ x ∈ productBox I, 0 < f x)
    (hf : ∀ R, (R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
      ∀ i u, (R i).upper u - (R i).lower u = (2 : ℝ) ^ (-k)) →
      ∀ x ∈ productBox R, ∀ y ∈ productBox R, f x = f y)
    (p : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 : ℝ) / 2) :
    eLpNorm (finiteFunctionMaximal G f) (ENNReal.ofReal p)
        (volume.restrict (productBox I)) ≤
      ENNReal.ofReal (maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1)) *
        eLpNorm f (ENNReal.ofReal p) (volume.restrict (productBox I)) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  obtain hnk | he := source_cutoff_or_empty hd D n k I hI G hG
  · let N := fun i => (k - n i).toNat
    have hfN : ProductLeafConstant I N f :=
      (source_productLeafConstant_iff hd D n k I hI hnk f).mpr hf
    have hGN : G ⊆ productDescendants I N := by
      intro R hR
      exact (source_productDescendants_iff hd D n k I hI hnk R).mpr (hG R hR)
    have hinput : (finiteInput I N f hfN).1 = f := by
      funext x
      by_cases hx : x ∈ productBox I
      · exact Set.indicator_of_mem hx f
      · change (productBox I).indicator f x = f x
        rw [Set.indicator_of_notMem hx, hs x hx]
    have hmax : finiteFunctionMaximal G f =
        finiteFamilyMaximal G (finiteInput I N f hfN) := by
      rw [← finiteFunctionMaximal_of_bounded, hinput]
    have hMN : ProductLeafConstant I N (finiteFunctionMaximal G f) := by
      rw [hmax]
      exact productLeafConstant_finiteFamilyMaximal I N G hGN _
    have hMpos (x) : 0 ≤ finiteFunctionMaximal G f x := by
      rw [hmax]
      exact finiteFamilyMaximal_nonneg G _ x
    have hf0 (x) : 0 ≤ f x := by
      by_cases hx : x ∈ productBox I
      · exact (hfpos x hx).le
      · rw [hs x hx]
    have hreal : lpNorm (finiteFunctionMaximal G f) (ENNReal.ofReal p)
          (volume.restrict (productBox I)) ≤
        (maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1)) *
          lpNorm f (ENNReal.ofReal p) (volume.restrict (productBox I)) := by
      rw [lpNorm_productLeafConstant_eq I N _ hMN p hp0,
        lpNorm_productLeafConstant_eq I N f hfN p hp0]
      simpa only [abs_of_nonneg (hMpos _), abs_of_nonneg (hf0 _)] using
        source_finite_incomparable_maximal_norm hm hd D n k I hI G hG hinc
          f hs hfpos hf p hp hp3
    have hK : 0 ≤ maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) := by
      apply mul_nonneg
      · unfold maximalDimensionConstant
        positivity
      · exact pow_nonneg (div_nonneg hp0.le (sub_pos.mpr hp).le) _
    rw [← ofReal_lpNorm (memLp_productLeafConstant I N _ hMN p hp0),
      ← ofReal_lpNorm (memLp_productLeafConstant I N f hfN p hp0)]
    simpa only [ENNReal.ofReal_mul hK] using ENNReal.ofReal_le_ofReal hreal
  · subst G
    have hz : finiteFunctionMaximal (∅ : Finset (∀ i, Box (Fin (d i)))) f = 0 := by
      funext x
      simp only [finiteFunctionMaximal, Finset.not_nonempty_empty, dite_false, Pi.zero_apply]
    rw [hz, eLpNorm_zero]
    exact zero_le

end ReyZygmund
