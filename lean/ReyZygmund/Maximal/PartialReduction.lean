import ReyZygmund.Maximal.FibreSquare
import ReyZygmund.Maximal.TopAverageRemainder
import ReyZygmund.Projection.TopAverageExpansion
import ReyZygmund.Geometry.ProductLp

/-!
# One partial signed maximum of the projected input

The partial difference sum is estimated by its fibre square. The
remaining nonempty top averages cost precisely one ordinary-maximal bound
each. All power integrals are over the finite top rectangle.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

private theorem partial_difference_sum_closure
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (A : Finset (Fin m))
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0) :
    ProductLeafConstant I N
        (∑ Q ∈ partialInterior I N A, productDifferenceMap A Q F).1 ∧
      ∀ x, x ∉ productBox I →
        (∑ Q ∈ partialInterior I N A, productDifferenceMap A Q F).1 x = 0 := by
  have hc Q (hQ : Q ∈ partialInterior I N A) :=
    productDifferenceMap_productStep_closure I N F hf hs A Q
      (fun i hi => partialInterior_mem_selected hQ hi)
  constructor
  · simpa only [Submodule.coe_sum] using
      productLeafConstant_finsetSum (partialInterior I N A)
        (fun Q => (productDifferenceMap A Q F).1) (fun Q hQ => (hc Q hQ).1)
  · intro x hx
    simp only [Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_eq_zero (fun Q hQ => (hc Q hQ).2 x hx)

private theorem root_average_closure
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (f : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N f.1)
    (hs : ∀ x, x ∉ productBox I → f.1 x = 0) (B : Finset (Fin m)) :
    ProductLeafConstant I N (productAverageMap B I f).1 ∧
      ∀ x, x ∉ productBox I → (productAverageMap B I f).1 x = 0 :=
  productAverageMap_productStep_closure I N f hf hs B I
    (fun i _ => mem_productDescendants.mp (root_mem_productDescendants I N) i)

private theorem projected_eq_difference_sum_sub_top_averages
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (f : boundedMeasurableFunctions d)
    (hf : ProductLeafConstant I N f.1)
    (hs : ∀ x, x ∉ productBox I → f.1 x = 0) (A : Finset (Fin m)) :
    finiteProjectionMap I N G f =
      (∑ Q ∈ partialInterior I N A,
        productDifferenceMap A Q (finiteProjectionMap I N G f)) -
      ∑ B ∈ A.powerset.erase ∅, (-1 : ℝ) ^ B.card • productAverageMap B I f := by
  have hc := finiteProjectionMap_productStep_closure I N G f hf hs
  have hg := partial_difference_sum_closure I N A _ hc.1 hc.2
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul,
    Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ productBox I
  · have h := finiteProjection_top_average_decomposition I N hd G f hf hs A x hx
    linarith
  · have hg0 := hg.2 x hx
    simp only [Submodule.coe_sum, Finset.sum_apply] at hg0
    rw [hc.2 x hx, hg0]
    have havg : (∑ B ∈ A.powerset.erase ∅,
        (-1 : ℝ) ^ B.card * (productAverageMap B I f).1 x) = 0 := by
      apply Finset.sum_eq_zero
      intro B _
      rw [(root_average_closure I N f hf hs B).2 x hx, mul_zero]
    rw [havg, sub_zero]

private theorem signed_maximal_sub_le
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (A : Finset (Fin m))
    (F H : boundedMeasurableFunctions d) (x : ProductPoint d) :
    finiteSignedPartialMaximal I N A (F - H) x ≤
      finiteSignedPartialMaximal I N A F x + finiteSignedPartialMaximal I N A H x := by
  apply Finset.sup'_le
  intro Q hQ
  change |(productAverageMap A Q (F - H)).1 x| ≤ _
  rw [map_sub]
  change |(productAverageMap A Q F).1 x - (productAverageMap A Q H).1 x| ≤ _
  have habs : |(productAverageMap A Q F).1 x - (productAverageMap A Q H).1 x| ≤
      |(productAverageMap A Q F).1 x| + |(productAverageMap A Q H).1 x| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le ((productAverageMap A Q F).1 x) (-(productAverageMap A Q H).1 x)
  exact habs.trans (add_le_add
    (Finset.le_sup' (fun R => |(productAverageMap A R F).1 x|) hQ)
    (Finset.le_sup' (fun R => |(productAverageMap A R H).1 x|) hQ))

private theorem signed_maximal_sum_le {α : Type*}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (A : Finset (Fin m))
    (s : Finset α) (F : α → boundedMeasurableFunctions d) (x : ProductPoint d) :
    finiteSignedPartialMaximal I N A (∑ a ∈ s, F a) x ≤
      ∑ a ∈ s, finiteSignedPartialMaximal I N A (F a) x := by
  apply Finset.sup'_le
  intro Q hQ
  change |(productAverageMap A Q (∑ a ∈ s, F a)).1 x| ≤ _
  simp only [map_sum, Submodule.coe_sum, Finset.sum_apply]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun a _ =>
    Finset.le_sup' (fun R => |(productAverageMap A R (F a)).1 x|) hQ))

private theorem signed_maximal_smul_le
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (A : Finset (Fin m))
    (F : boundedMeasurableFunctions d) (c : ℝ) (x : ProductPoint d) :
    finiteSignedPartialMaximal I N A (c • F) x ≤
      |c| * finiteSignedPartialMaximal I N A F x := by
  apply Finset.sup'_le
  intro Q hQ
  change |(productAverageMap A Q (c • F)).1 x| ≤ _
  rw [map_smul]
  change |c * (productAverageMap A Q F).1 x| ≤ _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (Finset.le_sup' (fun R => |(productAverageMap A R F).1 x|) hQ) (abs_nonneg c)

private theorem projected_partial_maximal_le
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (f : boundedMeasurableFunctions d)
    (hf : ProductLeafConstant I N f.1)
    (hs : ∀ x, x ∉ productBox I → f.1 x = 0)
    (A : Finset (Fin m)) (x : ProductPoint d) :
    finiteSignedPartialMaximal I N A (finiteProjectionMap I N G f) x ≤
      finiteSignedPartialMaximal I N A
        (∑ Q ∈ partialInterior I N A,
          productDifferenceMap A Q (finiteProjectionMap I N G f)) x +
      ∑ B ∈ A.powerset.erase ∅,
        finiteSignedPartialMaximal I N A (productAverageMap B I f) x := by
  have hdecomp := projected_eq_difference_sum_sub_top_averages I N hd G f hf hs A
  calc
    _ ≤ finiteSignedPartialMaximal I N A
          (∑ Q ∈ partialInterior I N A,
            productDifferenceMap A Q (finiteProjectionMap I N G f)) x +
        finiteSignedPartialMaximal I N A
          (∑ B ∈ A.powerset.erase ∅,
            (-1 : ℝ) ^ B.card • productAverageMap B I f) x := by
      conv_lhs => rw [hdecomp]
      exact signed_maximal_sub_le I N A _ _ x
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply (signed_maximal_sum_le I N A _ _ x).trans
      apply Finset.sum_le_sum
      intro B _
      simpa only [abs_pow, abs_neg, abs_one, one_pow, one_mul] using
        signed_maximal_smul_le I N A (productAverageMap B I f) ((-1 : ℝ) ^ B.card) x

private theorem signed_maximal_abs
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (A : Finset (Fin m))
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) :
    |finiteSignedPartialMaximal I N A F x| = finiteSignedPartialMaximal I N A F x :=
  abs_of_nonneg (finiteSignedPartialMaximal_nonneg I N A F x)

private theorem projected_partial_norm_le
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (f : boundedMeasurableFunctions d)
    (hf : ProductLeafConstant I N f.1)
    (hs : ∀ x, x ∉ productBox I → f.1 x = 0)
    (A : Finset (Fin m)) (p : ℝ) (hp : 1 ≤ p) :
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteSignedPartialMaximal I N A (finiteProjectionMap I N G f) x) p)
        (1 / p) ≤
      Real.rpow (∫ x in productBox I,
        Real.rpow (finiteSignedPartialMaximal I N A
          (∑ Q ∈ partialInterior I N A,
            productDifferenceMap A Q (finiteProjectionMap I N G f)) x) p) (1 / p) +
      ∑ B ∈ A.powerset.erase ∅,
        Real.rpow (∫ x in productBox I,
          Real.rpow (finiteSignedPartialMaximal I N A (productAverageMap B I f) x) p)
            (1 / p) := by
  let P := finiteProjectionMap I N G f
  let H := ∑ Q ∈ partialInterior I N A, productDifferenceMap A Q P
  let s := A.powerset.erase ∅
  let T (B : Finset (Fin m)) := finiteSignedPartialMaximal I N A (productAverageMap B I f)
  let V (x : ProductPoint d) := ∑ B ∈ s, T B x
  have hc := finiteProjectionMap_productStep_closure I N G f hf hs
  have hg := partial_difference_sum_closure I N A P hc.1 hc.2
  have hP := productLeafConstant_finiteSignedPartialMaximal I N A P hc.1 hc.2
  have hH := productLeafConstant_finiteSignedPartialMaximal I N A H hg.1 hg.2
  have hT (B : Finset (Fin m)) : ProductLeafConstant I N (T B) := by
    have hb := root_average_closure I N f hf hs B
    exact productLeafConstant_finiteSignedPartialMaximal I N A _ hb.1 hb.2
  have hV : ProductLeafConstant I N V := by
    intro Q hQ x hx y hy
    change (∑ B ∈ s, T B x) = ∑ B ∈ s, T B y
    exact Finset.sum_congr rfl (fun B _ => hT B Q hQ x hx y hy)
  have hV0 (x : ProductPoint d) : 0 ≤ V x :=
    Finset.sum_nonneg (fun B _ => finiteSignedPartialMaximal_nonneg I N A
      (productAverageMap B I f) x)
  have hAdd : ProductLeafConstant I N
      (fun x => finiteSignedPartialMaximal I N A H x + V x) := by
    intro Q hQ x hx y hy
    change finiteSignedPartialMaximal I N A H x + V x =
      finiteSignedPartialMaximal I N A H y + V y
    rw [hH Q hQ x hx y hy, hV Q hQ x hx y hy]
  have hmono := rootLp_mono I N (finiteSignedPartialMaximal I N A P)
    (fun x => finiteSignedPartialMaximal I N A H x + V x) hP hAdd
    (fun x _ => by
      rw [signed_maximal_abs, abs_of_nonneg
        (add_nonneg (finiteSignedPartialMaximal_nonneg I N A H x) (hV0 x))]
      exact projected_partial_maximal_le I N hd G f hf hs A x)
    p (zero_lt_one.trans_le hp)
  have htri := rootLp_add_le I N (finiteSignedPartialMaximal I N A H) V hH hV p hp
  have hsum := rootLp_sum_le I N s T (fun B _ => hT B) p hp
  have hsum' :
      Real.rpow (∫ x in productBox I, Real.rpow |V x| p) (1 / p) ≤
        ∑ B ∈ s, Real.rpow (∫ x in productBox I, Real.rpow (T B x) p) (1 / p) := by
    simpa only [V, T, signed_maximal_abs] using hsum
  have hbound := hmono.trans (htri.trans (add_le_add le_rfl hsum'))
  simpa only [P, H, T, s, signed_maximal_abs] using hbound

private theorem nonempty_complement_subsets_card (j : Fin m) :
    (((Finset.univ.erase j).powerset.erase ∅).card : ℝ) =
      (2 : ℝ) ^ (m - 1) - 1 := by
  have hA : (Finset.univ.erase j).card = m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  have h := Finset.card_erase_add_one
    (Finset.mem_powerset.mpr (Finset.empty_subset (Finset.univ.erase j)))
  rw [Finset.card_powerset, hA] at h
  have hcast : (((Finset.univ.erase j).powerset.erase ∅).card : ℝ) + 1 =
      (2 : ℝ) ^ (m - 1) := by exact_mod_cast h
  linarith

/-- The one-coordinate term in the maximal-to-square reduction, for a signed input and
arbitrary projection family. The remainder keeps the number of nonempty
top-average subsets and the ordinary-maximal exponent. -/
theorem finite_projected_partial_maximal_norm
    (hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (f : boundedMeasurableFunctions d)
    (hf : ProductLeafConstant I N f.1)
    (hs : ∀ x, x ∉ productBox I → f.1 x = 0)
    (j : Fin m) (p : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 : ℝ) / 2) :
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteSignedPartialMaximal I N (Finset.univ.erase j)
        (finiteProjectionMap I N G f) x) p) (1 / p) ≤
      (2 : ℝ) ^ (6 * (∑ i, d i) + 10) *
        Real.rpow (∫ x in productBox I,
          Real.rpow (finiteSquareFunction I N (Finset.univ.erase j)
            (finiteProjectionMap I N G f) x) p) (1 / p) +
      ((2 : ℝ) ^ (m - 1) - 1) * (p / (p - 1)) ^ (m - 2) *
        Real.rpow (∫ x in productBox I, Real.rpow |f.1 x| p) (1 / p) := by
  cases m with
  | zero => omega
  | succ n =>
    let A : Finset (Fin (n + 1)) := Finset.univ.erase j
    let P := finiteProjectionMap I N G f
    have hc := finiteProjectionMap_productStep_closure I N G f hf hs
    have hsplit := projected_partial_norm_le I N hd G f hf hs A p hp.le
    have hfibre := finite_partial_difference_sum_square_lp I N hd P hc.1 hc.2 j p hp.le hp3
    have hrem :
        (∑ B ∈ A.powerset.erase ∅,
          Real.rpow (∫ x in productBox I,
            Real.rpow (finiteSignedPartialMaximal I N A (productAverageMap B I f) x) p)
              (1 / p)) ≤
        ((2 : ℝ) ^ (n + 1 - 1) - 1) * (p / (p - 1)) ^ (n + 1 - 2) *
          Real.rpow (∫ x in productBox I, Real.rpow |f.1 x| p) (1 / p) := by
      calc
        _ ≤ ∑ _B ∈ A.powerset.erase ∅,
            (p / (p - 1)) ^ (n + 1 - 2) *
              Real.rpow (∫ x in productBox I, Real.rpow |f.1 x| p) (1 / p) := by
          apply Finset.sum_le_sum
          intro B hB
          have hBA : B ⊆ Finset.univ.erase j :=
            Finset.mem_powerset.mp (Finset.mem_erase.mp hB).2
          have hBne : B.Nonempty :=
            Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hB).1
          exact finiteSignedPartialMaximal_topAverage_norm hm I N hd j B hBA hBne
            f hf hs p hp
        _ = ((A.powerset.erase ∅).card : ℝ) *
            ((p / (p - 1)) ^ (n + 1 - 2) *
              Real.rpow (∫ x in productBox I, Real.rpow |f.1 x| p) (1 / p)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ = _ := by
          rw [show ((A.powerset.erase ∅).card : ℝ) =
            (2 : ℝ) ^ (n + 1 - 1) - 1 from nonempty_complement_subsets_card j]
          ring
    exact hsplit.trans (add_le_add hfibre hrem)

end ReyZygmund
