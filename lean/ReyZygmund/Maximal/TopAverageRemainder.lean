import ReyZygmund.Maximal.PartialSigned
import ReyZygmund.Geometry.RootAverageLp
import ReyZygmund.Geometry.ProductIntegrability

/-! # Top-cube averages in the maximal-to-square reduction

An average over a top cube is constant in that coordinate on the cube. Averages
over smaller cubes recover the value on their support and vanish elsewhere. Those
coordinates can be omitted from the signed maximum. Iterated coordinate maximal
estimates and the norm contraction for top-cube averages give the remainder bound.


-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

private theorem product_average_commute_coordinate
    (A : Finset (Fin m)) (j : Fin m) (hj : j ∉ A)
    (Q : ∀ i, Box (Fin (d i))) (R : Box (Fin (d j))) :
    productAverageMap A Q * averageMap j R =
      averageMap j R * productAverageMap A Q := by
  revert hj
  induction A using Finset.induction_on with
  | empty => intro _; simp
  | @insert i A hi ih =>
    intro hj
    have hjA : j ∉ A := fun h => hj (Finset.mem_insert_of_mem h)
    have hji : j ≠ i := fun h => hj (Finset.mem_insert.mpr (Or.inl h))
    rw [productAverageMap_insert A i hi Q, mul_assoc, ih hjA, ← mul_assoc,
      (averageMap_commute i j hji.symm (Q i) R).eq, mul_assoc]

private theorem product_average_extract
    (A : Finset (Fin m)) (j : Fin m) (hj : j ∈ A)
    (Q : ∀ i, Box (Fin (d i))) :
    productAverageMap A Q = averageMap j (Q j) * productAverageMap (A.erase j) Q := by
  simpa only [Finset.insert_erase hj] using
    productAverageMap_insert (A.erase j) j (Finset.notMem_erase j A) Q

private theorem coordinate_average_root_average_of_mem
    (j : Fin m) (I Q : Box (Fin (d j))) (hQI : Q ≤ I)
    (F : boundedMeasurableFunctions d) (x : ProductPoint d) (hx : x j ∈ Q) :
    (averageMap j Q (averageMap j I F)).1 x = (averageMap j I F).1 x := by
  rw [averageMap_apply, coordinateAverage_of_mem j Q _ x hx]
  have hc : ∀ y ∈ Q, (averageMap j I F).1 (Function.update x j y) =
      (averageMap j I F).1 x := by
    intro y hy
    simp only [averageMap_apply]
    rw [coordinateAverage_of_mem j I F.1 _ (by simpa using hQI hy),
      coordinateAverage_of_mem j I F.1 x (hQI hx)]
    simp only [Function.update_idem]
  rw [setIntegral_congr_fun Q.measurableSet_coe hc, setIntegral_const, smul_eq_mul]
  exact mul_div_cancel_left₀ _ (box_volume_pos Q).ne'

private theorem erase_root_average_le
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (B A : Finset (Fin m))
    (j : Fin m) (hjB : j ∈ B) (hjA : j ∈ A) (x : ProductPoint d) :
    finiteSignedPartialMaximal I N A (productAverageMap B I F) x ≤
      finiteSignedPartialMaximal I N (A.erase j) (productAverageMap B I F) x := by
  apply Finset.sup'_le
  intro Q hQ
  change |(productAverageMap A Q (productAverageMap B I F)).1 x| ≤ _
  rw [product_average_extract A j hjA Q, Module.End.mul_apply]
  have hc : productAverageMap (A.erase j) Q (productAverageMap B I F) =
      averageMap j (I j)
        (productAverageMap (A.erase j) Q (productAverageMap (B.erase j) I F)) := by
    rw [product_average_extract B j hjB I, Module.End.mul_apply]
    exact congrArg
      (fun T : Module.End ℝ (boundedMeasurableFunctions d) =>
        T (productAverageMap (B.erase j) I F))
      (product_average_commute_coordinate (A.erase j) j (Finset.notMem_erase j A)
        Q (I j))
  by_cases hxQ : x j ∈ Q j
  · have heq : (averageMap j (Q j)
        (productAverageMap (A.erase j) Q (productAverageMap B I F))).1 x =
        (productAverageMap (A.erase j) Q (productAverageMap B I F)).1 x := by
      simpa only [hc] using coordinate_average_root_average_of_mem j (I j) (Q j)
        (le_of_mem_descendants (mem_productDescendants.mp hQ j))
        (productAverageMap (A.erase j) Q (productAverageMap (B.erase j) I F)) x hxQ
    rw [heq]
    exact Finset.le_sup'
      (fun R => |(productAverageMap (A.erase j) R (productAverageMap B I F)).1 x|) hQ
  · rw [averageMap_apply, coordinateAverage_of_notMem j (Q j) _ x hxQ, abs_zero]
    exact finiteSignedPartialMaximal_nonneg I N (A.erase j) (productAverageMap B I F) x

private theorem remove_root_averages_le
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (B D : Finset (Fin m))
    (hDB : D ⊆ B) (A : Finset (Fin m)) (hDA : D ⊆ A) (x : ProductPoint d) :
    finiteSignedPartialMaximal I N A (productAverageMap B I F) x ≤
      finiteSignedPartialMaximal I N (A \ D) (productAverageMap B I F) x := by
  revert hDB A
  induction D using Finset.induction_on with
  | empty => intro _ A _; simp
  | @insert j D hj ih =>
    intro hDB A hDA
    have hjB : j ∈ B := hDB (Finset.mem_insert_self j D)
    have hjA : j ∈ A := hDA (Finset.mem_insert_self j D)
    have hDB' : D ⊆ B := fun i hi => hDB (Finset.mem_insert_of_mem hi)
    have hDA' : D ⊆ A.erase j := by
      intro i hi
      exact Finset.mem_erase.mpr
        ⟨ne_of_mem_of_not_mem hi hj, hDA (Finset.mem_insert_of_mem hi)⟩
    have hrec := ih hDB' (A.erase j) hDA'
    have hset : A.erase j \ D = A \ insert j D := by
      rw [Finset.erase_sdiff_comm, ← Finset.sdiff_insert]
    rw [hset] at hrec
    exact (erase_root_average_le I N F B A j hjB hjA x).trans hrec

/-- Coordinates already averaged over top cubes can be omitted from the signed maximum
on the top rectangle. Smaller averages recover their values on their supports. -/
theorem finiteSignedPartialMaximal_rootAverage_eq
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A B : Finset (Fin m)) (hBA : B ⊆ A)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (x : ProductPoint d) (hx : x ∈ productBox I) :
    finiteSignedPartialMaximal I N A (productAverageMap B I F) x =
      finiteSignedPartialMaximal I N (A \ B) (productAverageMap B I F) x := by
  apply le_antisymm
  · exact remove_root_averages_le I N F B B (fun _ h => h) A hBA x
  · have hc := productAverageMap_productStep_closure I N F hf hs B I
      (fun i _ => mem_productDescendants.mp (root_mem_productDescendants I N) i)
    exact finiteSignedPartialMaximal_mono I N (productAverageMap B I F) hc.1 hc.2
      (A \ B) A Finset.sdiff_subset x hx

private theorem signed_partial_maximal_integral
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A : Finset (Fin m)) (hd : ∀ i ∈ A, 0 < d i)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (p : ℝ) (hp : 1 < p) :
    (∫ x in productBox I, Real.rpow (finiteSignedPartialMaximal I N A F x) p) ≤
      Real.rpow (p / (p - 1)) (p * (A.card : ℝ)) *
        ∫ x in productBox I, Real.rpow |F.1 x| p := by
  let g := A.toList.foldr (fun i h => coordinateDyadicMaximal i (I i) (N i) h) F.1
  have hg : ProductLeafConstant I N g :=
    productLeafConstant_foldr_coordinateDyadicMaximal I N A.toList F.1 hf
  have hM := productLeafConstant_finiteSignedPartialMaximal I N A F hf hs
  have hMI : IntegrableOn
      (fun x => Real.rpow (finiteSignedPartialMaximal I N A F x) p)
      (productBox I) volume := by
    apply integrableOn_productLeafConstant I N
    intro Q hQ x hx y hy
    exact congrArg (fun t => Real.rpow t p) (hM Q hQ x hx y hy)
  have hgI : IntegrableOn (fun x => Real.rpow |g x| p) (productBox I) volume := by
    apply integrableOn_productLeafConstant I N
    intro Q hQ x hx y hy
    exact congrArg (fun t => Real.rpow |t| p) (hg Q hQ x hx y hy)
  calc
    _ ≤ ∫ x in productBox I, Real.rpow |g x| p := by
      apply setIntegral_mono_on hMI hgI (measurableSet_productBox I)
      intro x hx
      apply Real.rpow_le_rpow (finiteSignedPartialMaximal_nonneg I N A F x) _
        (le_trans zero_le_one hp.le)
      apply Finset.sup'_le
      intro Q hQ
      have h := productAverageMap_abs_le_iteratedMaximal I N F hf hs
        A.toList A.nodup_toList Q
        (fun i _ => mem_productDescendants.mp hQ i) x hx
      simpa only [Finset.toList_toFinset, g] using h
    _ ≤ _ := by
      have h := finite_iterated_coordinate_maximal_integral I N A.toList
        (fun i hi => hd i (Finset.mem_toList.mp hi)) F.1 hf p hp
      simpa only [Finset.length_toList, g] using h

/-- Each already averaged coordinate is omitted from the exact ordinary
maximal exponent. Only the dimensions of the remaining coordinates need
be positive. The original input may be signed. -/
theorem finiteSignedPartialMaximal_topAverage_integral
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (A B : Finset (Fin m)) (hBA : B ⊆ A)
    (hd : ∀ i ∈ A \ B, 0 < d i)
    (F : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N F.1)
    (hs : ∀ x, x ∉ productBox I → F.1 x = 0)
    (p : ℝ) (hp : 1 < p) :
    (∫ x in productBox I,
      Real.rpow (finiteSignedPartialMaximal I N A (productAverageMap B I F) x) p) ≤
      Real.rpow (p / (p - 1)) (p * ((A \ B).card : ℝ)) *
        ∫ x in productBox I, Real.rpow |F.1 x| p := by
  have hc := productAverageMap_productStep_closure I N F hf hs B I
    (fun i _ => mem_productDescendants.mp (root_mem_productDescendants I N) i)
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hcoeff : 0 ≤ Real.rpow (p / (p - 1)) (p * ((A \ B).card : ℝ)) :=
    Real.rpow_nonneg (div_nonneg hp0.le (sub_pos.mpr hp).le) _
  calc
    _ = ∫ x in productBox I,
        Real.rpow (finiteSignedPartialMaximal I N (A \ B)
          (productAverageMap B I F) x) p := by
      apply setIntegral_congr_fun (measurableSet_productBox I)
      intro x hx
      exact congrArg (fun t => Real.rpow t p)
        (finiteSignedPartialMaximal_rootAverage_eq I N A B hBA F hf hs x hx)
    _ ≤ Real.rpow (p / (p - 1)) (p * ((A \ B).card : ℝ)) *
        ∫ x in productBox I, Real.rpow |(productAverageMap B I F).1 x| p :=
      signed_partial_maximal_integral I N (A \ B) hd (productAverageMap B I F)
        hc.1 hc.2 p hp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (productRootAverage_integral_rpow I N F hf B p hp.le) hcoeff

/-- Source top-average remainder bound for each nonempty subset of the
coordinates complementary to j. All real exponents p > 1 are allowed. -/
theorem finiteSignedPartialMaximal_topAverage_norm
    (hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (j : Fin m) (B : Finset (Fin m))
    (hBA : B ⊆ Finset.univ.erase j) (hB : B.Nonempty)
    (f : boundedMeasurableFunctions d) (hf : ProductLeafConstant I N f.1)
    (hs : ∀ x, x ∉ productBox I → f.1 x = 0)
    (p : ℝ) (hp : 1 < p) :
    Real.rpow (∫ x in productBox I,
      Real.rpow (finiteSignedPartialMaximal I N (Finset.univ.erase j)
        (productAverageMap B I f) x) p) (1 / p) ≤
      (p / (p - 1)) ^ (m - 2) *
        Real.rpow (∫ x in productBox I, Real.rpow |f.1 x| p) (1 / p) := by
  let c := p / (p - 1)
  let k := ((Finset.univ.erase j) \ B).card
  let Y := ∫ x in productBox I, Real.rpow |f.1 x| p
  let L := ∫ x in productBox I,
    Real.rpow (finiteSignedPartialMaximal I N (Finset.univ.erase j)
      (productAverageMap B I f) x) p
  change Real.rpow L (1 / p) ≤ c ^ (m - 2) * Real.rpow Y (1 / p)
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hc1 : 1 ≤ c := by
    apply (le_div_iff₀ (sub_pos.mpr hp)).mpr
    linarith
  have hc0 : 0 ≤ c := zero_le_one.trans hc1
  have hL0 : 0 ≤ L := integral_nonneg (fun x =>
    Real.rpow_nonneg (finiteSignedPartialMaximal_nonneg I N (Finset.univ.erase j)
      (productAverageMap B I f) x) p)
  have hY0 : 0 ≤ Y := integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg (f.1 x)) p)
  have hbound := finiteSignedPartialMaximal_topAverage_integral I N (Finset.univ.erase j)
    B hBA (fun i _ => hd i) f hf hs p hp
  change L ≤ Real.rpow c (p * (k : ℝ)) * Y at hbound
  have hcard : k ≤ m - 2 := by
    dsimp only [k]
    rw [Finset.card_sdiff_of_subset hBA, Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin]
    have hBpos : 0 < B.card := Finset.card_pos.mpr hB
    omega
  have hexp : (p * (k : ℝ)) * (1 / p) = (k : ℝ) := by
    calc
      _ = (p * (k : ℝ)) / p := by ring
      _ = _ := mul_div_cancel_left₀ _ hp0.ne'
  have hcoeff : Real.rpow c (k : ℝ) ≤ c ^ (m - 2) := by
    have hk : (k : ℝ) ≤ ((m - 2 : ℕ) : ℝ) := by exact_mod_cast hcard
    calc
      _ ≤ Real.rpow c ((m - 2 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hc1 hk
      _ = _ := Real.rpow_natCast c (m - 2)
  calc
    _ ≤ Real.rpow (Real.rpow c (p * (k : ℝ)) * Y) (1 / p) :=
      Real.rpow_le_rpow hL0 hbound (one_div_nonneg.mpr hp0.le)
    _ = Real.rpow c (k : ℝ) * Real.rpow Y (1 / p) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.mul_rpow (Real.rpow_nonneg hc0 _) hY0, ← Real.rpow_mul hc0, hexp]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hY0 _)

end ReyZygmund
