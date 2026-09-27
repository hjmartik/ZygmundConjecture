import ReyZygmund.Geometry.FiniteAverages
import ReyZygmund.Weighted.Scalar

/-! # The one-coordinate weighted square estimate

The finite dyadic cubes, their dyadic children and Lebesgue averages give the
weighted square inequality with the paper's quantitative constant.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry

variable {d : ℕ}

/-- The scalar average occurring inside the supported averaging operator. -/
private noncomputable def boxMean (Q : Box (Fin d)) (g : (Fin d → ℝ) → ℝ) : ℝ :=
  (∫ x in (Q : Set (Fin d → ℝ)), g x) / volume.real (Q : Set (Fin d → ℝ))

private lemma volume_mul_boxMean (Q : Box (Fin d)) (g : (Fin d → ℝ) → ℝ) :
    volume.real (Q : Set (Fin d → ℝ)) * boxMean Q g =
      ∫ x in (Q : Set (Fin d → ℝ)), g x := by
  unfold boxMean
  field_simp [ne_of_gt (box_volume_pos Q)]

private lemma boxAverage_apply_mem (Q : Box (Fin d)) (g : (Fin d → ℝ) → ℝ)
    {x : Fin d → ℝ} (hx : x ∈ Q) : boxAverage Q g x = boxMean Q g := by
  simp [boxAverage, boxMean, hx]

private lemma boxMean_of_constant (Q : Box (Fin d)) (g : (Fin d → ℝ) → ℝ)
    (hg : ∀ x ∈ Q, ∀ y ∈ Q, g x = g y) {x : Fin d → ℝ} (hx : x ∈ Q) :
    boxMean Q g = g x := by
  have h := congrFun (boxAverage_of_constant Q g hg) x
  simpa [boxAverage, boxMean, hx] using h

private lemma sum_integral_partition {I : Box (Fin d)} (π : Prepartition I)
    (hπ : π.IsPartition) (g : (Fin d → ℝ) → ℝ)
    (hg : IntegrableOn g (I : Set (Fin d → ℝ)) volume) :
    (∑ Q ∈ π.boxes, ∫ x in (Q : Set (Fin d → ℝ)), g x) =
      ∫ x in (I : Set (Fin d → ℝ)), g x := by
  rw [← hπ.iUnion_eq, Prepartition.iUnion_def]
  exact (integral_biUnion_finset π.boxes
    (fun Q _ => Q.measurableSet_coe) π.pairwiseDisjoint
    (fun Q hQ => hg.mono_set (π.le_of_mem hQ))).symm

private lemma sum_volume_partition {I : Box (Fin d)} (π : Prepartition I)
    (hπ : π.IsPartition) :
    (∑ Q ∈ π.boxes, volume.real (Q : Set (Fin d → ℝ))) =
      volume.real (I : Set (Fin d → ℝ)) := by
  simpa only [hπ.iUnion_eq] using (π.measure_iUnion_toReal volume).symm

private lemma sum_volume_mul_boxMean {I : Box (Fin d)} (π : Prepartition I)
    (hπ : π.IsPartition) (g : (Fin d → ℝ) → ℝ)
    (hg : IntegrableOn g (I : Set (Fin d → ℝ)) volume) :
    (∑ Q ∈ π.boxes, volume.real (Q : Set (Fin d → ℝ)) * boxMean Q g) =
      volume.real (I : Set (Fin d → ℝ)) * boxMean I g := by
  simp_rw [volume_mul_boxMean]
  exact sum_integral_partition π hπ g hg

private lemma sum_volume_mul_mean_sub {I : Box (Fin d)} (π : Prepartition I)
    (hπ : π.IsPartition) (g : (Fin d → ℝ) → ℝ)
    (hg : IntegrableOn g (I : Set (Fin d → ℝ)) volume) :
    (∑ Q ∈ π.boxes, volume.real (Q : Set (Fin d → ℝ)) *
      (boxMean Q g - boxMean I g)) = 0 := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, sum_volume_mul_boxMean π hπ g hg,
    ← Finset.sum_mul, sum_volume_partition π hπ, sub_self]

private lemma child_volume {Q R : Box (Fin d)}
    (hR : R ∈ Prepartition.splitCenter Q) :
    volume.real (R : Set (Fin d → ℝ)) =
      volume.real (Q : Set (Fin d → ℝ)) / (2 : ℝ) ^ d := by
  simp only [measureReal_def, Box.volume_apply']
  simp_rw [Prepartition.upper_sub_lower_of_mem_splitCenter hR]
  rw [Finset.prod_div_distrib]
  simp

private lemma integral_eq_volume_mul {Q : Box (Fin d)}
    {g : (Fin d → ℝ) → ℝ} {c : ℝ} (hg : ∀ x ∈ Q, g x = c) :
    (∫ x in (Q : Set (Fin d → ℝ)), g x) =
      volume.real (Q : Set (Fin d → ℝ)) * c := by
  calc
    _ = ∫ _ in (Q : Set (Fin d → ℝ)), c :=
      setIntegral_congr_fun Q.measurableSet_coe hg
    _ = _ := by rw [setIntegral_const, smul_eq_mul]

private lemma integrableOn_partition_constant {I : Box (Fin d)} (π : Prepartition I)
    (hπ : π.IsPartition) (g : (Fin d → ℝ) → ℝ)
    (hg : ∀ Q ∈ π.boxes, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y) :
    IntegrableOn g (I : Set (Fin d → ℝ)) volume := by
  rw [← hπ.iUnion_eq, Prepartition.iUnion_def]
  apply integrableOn_finset_iUnion.mpr
  intro Q hQ
  have hc : IntegrableOn (fun _ : Fin d → ℝ => g Q.upper)
      (Q : Set (Fin d → ℝ)) volume :=
    integrableOn_const (Q.measure_coe_lt_top volume).ne
  exact hc.congr_fun (fun x hx => hg Q hQ Q.upper Q.upper_mem x hx) Q.measurableSet_coe

private lemma boxMean_pos (Q : Box (Fin d)) (g : (Fin d → ℝ) → ℝ)
    (hg : IntegrableOn g (Q : Set (Fin d → ℝ)) volume)
    (hpos : ∀ x ∈ Q, 0 < g x) : 0 < boxMean Q g := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Q : Set (Fin d → ℝ))] g :=
    (ae_restrict_iff' Q.measurableSet_coe).mpr
      (Filter.Eventually.of_forall fun x hx => (hpos x hx).le)
  have hsupp : Function.support g ∩ (Q : Set (Fin d → ℝ)) = Q := by
    ext x
    constructor
    · exact And.right
    · intro hx
      exact ⟨ne_of_gt (hpos x hx), hx⟩
  unfold boxMean
  apply div_pos ?_ (box_volume_pos Q)
  apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hg).mpr
  rw [hsupp]
  exact (ENNReal.toReal_pos_iff.mp (box_volume_pos Q)).1

private lemma boxMean_child_le {Q R : Box (Fin d)}
    (hR : R ∈ Prepartition.splitCenter Q) (g : (Fin d → ℝ) → ℝ)
    (hg : IntegrableOn g (Q : Set (Fin d → ℝ)) volume)
    (hnonneg : ∀ x ∈ Q, 0 ≤ g x) :
    boxMean R g ≤ (2 : ℝ) ^ d * boxMean Q g := by
  have hle : (R : Set (Fin d → ℝ)) ⊆ Q := (Prepartition.splitCenter Q).le_of_mem hR
  have hnn : 0 ≤ᵐ[volume.restrict (Q : Set (Fin d → ℝ))] g :=
    (ae_restrict_iff' Q.measurableSet_coe).mpr
      (Filter.Eventually.of_forall hnonneg)
  have hi := setIntegral_mono_set hg hnn (Filter.Eventually.of_forall hle)
  unfold boxMean
  rw [child_volume hR]
  apply (div_le_iff₀ (div_pos (box_volume_pos Q) (pow_pos (by norm_num) d))).mpr
  calc
    _ ≤ ∫ x in (Q : Set (Fin d → ℝ)), g x := hi
    _ = (2 : ℝ) ^ d *
        ((∫ x in (Q : Set (Fin d → ℝ)), g x) / volume.real (Q : Set (Fin d → ℝ))) *
        (volume.real (Q : Set (Fin d → ℝ)) / (2 : ℝ) ^ d) := by
      field_simp [ne_of_gt (box_volume_pos Q), ne_of_gt (pow_pos (by norm_num : (0 : ℝ) < 2) d)]

private lemma boxDifference_apply_child {Q R : Box (Fin d)}
    (hR : R ∈ Prepartition.splitCenter Q) (g : (Fin d → ℝ) → ℝ)
    {x : Fin d → ℝ} (hx : x ∈ R) :
    boxDifference Q g x = boxMean R g - boxMean Q g := by
  classical
  have hxQ : x ∈ Q := (Prepartition.splitCenter Q).le_of_mem hR hx
  simp only [boxDifference, Pi.sub_apply, Finset.sum_apply]
  rw [Finset.sum_eq_single R]
  · rw [boxAverage_apply_mem R g hx, boxAverage_apply_mem Q g hxQ]
  · intro S hS hSR
    have hxS : x ∉ S := fun h =>
      hSR ((Prepartition.splitCenter Q).eq_of_mem_of_mem hS hR h hx)
    simp [boxAverage, hxS]
  · simp [hR]

private lemma difference_quotient_integrable (Q : Box (Fin d))
    (u : (Fin d → ℝ) → ℝ) (b r : ℝ) :
    IntegrableOn (fun x => (boxDifference Q u x) ^ 2 / Real.rpow b r)
      (Q : Set (Fin d → ℝ)) volume := by
  apply integrableOn_partition_constant (Prepartition.splitCenter Q)
    (Prepartition.isPartition_splitCenter Q)
  intro R hR x hx y hy
  rw [boxDifference_apply_child hR u hx, boxDifference_apply_child hR u hy]

private lemma integral_difference_square (Q : Box (Fin d))
    (u : (Fin d → ℝ) → ℝ) (b r : ℝ) :
    (∫ x in (Q : Set (Fin d → ℝ)), (boxDifference Q u x) ^ 2 / Real.rpow b r) =
      ∑ R ∈ (Prepartition.splitCenter Q).boxes,
        volume.real (R : Set (Fin d → ℝ)) * (boxMean R u - boxMean Q u) ^ 2 /
          Real.rpow b r := by
  rw [← sum_integral_partition (Prepartition.splitCenter Q)
    (Prepartition.isPartition_splitCenter Q)
    (fun x => (boxDifference Q u x) ^ 2 / Real.rpow b r)
    (difference_quotient_integrable Q u b r)]
  apply Finset.sum_congr rfl
  intro R hR
  calc
    _ = volume.real (R : Set (Fin d → ℝ)) *
        ((boxMean R u - boxMean Q u) ^ 2 / Real.rpow b r) :=
      integral_eq_volume_mul (fun x hx => by rw [boxDifference_apply_child hR u hx])
    _ = _ := by ring

private lemma energy_integrable (I : Box (Fin d)) (N : ℕ)
    (u v : (Fin d → ℝ) → ℝ) (p : ℝ)
    (hu : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, u x = u y)
    (hv : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, v x = v y) :
    IntegrableOn (fun x => (u x) ^ 2 / Real.rpow (v x) (2 - p))
      (I : Set (Fin d → ℝ)) volume := by
  apply integrableOn_of_leafConstant I N
  intro Q hQ x hx y hy
  rw [hu Q hQ x hx y hy, hv Q hQ x hx y hy]

/-- The scalar remainder with the exact dyadic child-to-parent factor. -/
private lemma scalar_pair_estimate (d : ℕ) (p a₀ a₁ b₀ b₁ : ℝ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁)
    (hratio : b₁ ≤ (2 : ℝ) ^ d * b₀) :
    (a₁ - a₀) ^ 2 / Real.rpow b₀ (2 - p) ≤
      (Real.rpow 2 ((d : ℝ) * (2 - p)) * ((3 - p) / (p - 1))) *
        (scalarPsi p a₁ b₁ - scalarPsi p a₀ b₀ -
          2 * a₀ * (a₁ - a₀) / Real.rpow b₀ (2 - p) +
          (2 - p) * a₀ ^ 2 * (b₁ - b₀) / Real.rpow b₀ (3 - p)) := by
  have hp1 : 0 < p - 1 := by linarith
  have h3p : 0 < 3 - p := by linarith
  have htwo : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hmax : max b₀ b₁ ≤ (2 : ℝ) ^ d * b₀ := by
    apply max_le _ hratio
    calc
      b₀ = 1 * b₀ := by ring
      _ ≤ (2 : ℝ) ^ d * b₀ := mul_le_mul_of_nonneg_right htwo hb₀.le
  have hmaxpos : 0 < max b₀ b₁ := lt_of_lt_of_le hb₀ (le_max_left _ _)
  have hD : 0 < Real.rpow 2 ((d : ℝ) * (2 - p)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hmaxpow : 0 < Real.rpow (max b₀ b₁) (2 - p) :=
    Real.rpow_pos_of_pos hmaxpos _
  have hpow : Real.rpow (max b₀ b₁) (2 - p) ≤
      Real.rpow 2 ((d : ℝ) * (2 - p)) * Real.rpow b₀ (2 - p) := by
    calc
      _ ≤ Real.rpow ((2 : ℝ) ^ d * b₀) (2 - p) :=
        Real.rpow_le_rpow hmaxpos.le hmax (sub_nonneg.mpr hp2)
      _ = Real.rpow ((2 : ℝ) ^ d) (2 - p) * Real.rpow b₀ (2 - p) :=
        Real.mul_rpow (x := (2 : ℝ) ^ d) (y := b₀) (z := 2 - p)
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d) hb₀.le
      _ = _ := congrArg (fun t : ℝ => t * Real.rpow b₀ (2 - p))
        (Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) d (2 - p)).symm
  have hdiv := div_le_div_of_nonneg_left (sq_nonneg (a₁ - a₀)) hmaxpow hpow
  have hcompare : (a₁ - a₀) ^ 2 / Real.rpow b₀ (2 - p) ≤
      Real.rpow 2 ((d : ℝ) * (2 - p)) *
        ((a₁ - a₀) ^ 2 / Real.rpow (max b₀ b₁) (2 - p)) := by
    calc
      _ = Real.rpow 2 ((d : ℝ) * (2 - p)) *
          ((a₁ - a₀) ^ 2 /
            (Real.rpow 2 ((d : ℝ) * (2 - p)) * Real.rpow b₀ (2 - p))) := by
        rw [← mul_div_assoc, mul_div_mul_left _ _ (ne_of_gt hD)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiv hD.le
  have hs := scalar_estimate p a₀ (a₁ - a₀) b₀ (b₁ - b₀) hp hp2 hb₀ (by linarith)
  have haeq : a₀ + (a₁ - a₀) = a₁ := by ring
  have hbeq : b₀ + (b₁ - b₀) = b₁ := by ring
  rw [haeq, hbeq] at hs
  have hK : 0 ≤ Real.rpow 2 ((d : ℝ) * (2 - p)) * ((3 - p) / (p - 1)) :=
    mul_nonneg hD.le (div_nonneg h3p.le hp1.le)
  calc
    _ ≤ Real.rpow 2 ((d : ℝ) * (2 - p)) *
        ((a₁ - a₀) ^ 2 / Real.rpow (max b₀ b₁) (2 - p)) := hcompare
    _ = (Real.rpow 2 ((d : ℝ) * (2 - p)) * ((3 - p) / (p - 1))) *
        ((p - 1) / (3 - p) *
          ((a₁ - a₀) ^ 2 / Real.rpow (max b₀ b₁) (2 - p))) := by
      field_simp [ne_of_gt hp1, ne_of_gt h3p, ne_of_gt hmaxpow]
    _ ≤ _ := mul_le_mul_of_nonneg_left hs hK

/-- Summing over children cancels both linear increments. -/
private lemma weighted_parent_step (Q : Box (Fin d))
    (u v : (Fin d → ℝ) → ℝ) (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2)
    (hu : IntegrableOn u (Q : Set (Fin d → ℝ)) volume)
    (hv : IntegrableOn v (Q : Set (Fin d → ℝ)) volume)
    (hvpos : ∀ x ∈ Q, 0 < v x) :
    (∫ x in (Q : Set (Fin d → ℝ)),
        (boxDifference Q u x) ^ 2 / Real.rpow (boxMean Q v) (2 - p)) ≤
      (Real.rpow 2 ((d : ℝ) * (2 - p)) * ((3 - p) / (p - 1))) *
        ((∑ R ∈ (Prepartition.splitCenter Q).boxes,
            volume.real (R : Set (Fin d → ℝ)) * scalarPsi p (boxMean R u) (boxMean R v)) -
          volume.real (Q : Set (Fin d → ℝ)) * scalarPsi p (boxMean Q u) (boxMean Q v)) := by
  have hpair (R : Box (Fin d)) (hR : R ∈ (Prepartition.splitCenter Q).boxes) :=
    scalar_pair_estimate d p (boxMean Q u) (boxMean R u) (boxMean Q v) (boxMean R v)
      hp hp2 (boxMean_pos Q v hv hvpos)
      (boxMean_pos R v (hv.mono_set ((Prepartition.splitCenter Q).le_of_mem hR))
        (fun x hx => hvpos x ((Prepartition.splitCenter Q).le_of_mem hR hx)))
      (boxMean_child_le hR v hv (fun x hx => (hvpos x hx).le))
  have hcancel :
      (∑ R ∈ (Prepartition.splitCenter Q).boxes,
        volume.real (R : Set (Fin d → ℝ)) *
          (scalarPsi p (boxMean R u) (boxMean R v) -
            scalarPsi p (boxMean Q u) (boxMean Q v) -
            2 * boxMean Q u * (boxMean R u - boxMean Q u) /
              Real.rpow (boxMean Q v) (2 - p) +
            (2 - p) * (boxMean Q u) ^ 2 * (boxMean R v - boxMean Q v) /
              Real.rpow (boxMean Q v) (3 - p))) =
        (∑ R ∈ (Prepartition.splitCenter Q).boxes,
          volume.real (R : Set (Fin d → ℝ)) * scalarPsi p (boxMean R u) (boxMean R v)) -
        volume.real (Q : Set (Fin d → ℝ)) * scalarPsi p (boxMean Q u) (boxMean Q v) := by
    calc
      _ = (∑ R ∈ (Prepartition.splitCenter Q).boxes,
            volume.real (R : Set (Fin d → ℝ)) * scalarPsi p (boxMean R u) (boxMean R v)) -
          (∑ R ∈ (Prepartition.splitCenter Q).boxes, volume.real (R : Set (Fin d → ℝ))) *
            scalarPsi p (boxMean Q u) (boxMean Q v) -
          (2 * boxMean Q u / Real.rpow (boxMean Q v) (2 - p)) *
            (∑ R ∈ (Prepartition.splitCenter Q).boxes,
              volume.real (R : Set (Fin d → ℝ)) * (boxMean R u - boxMean Q u)) +
          ((2 - p) * (boxMean Q u) ^ 2 / Real.rpow (boxMean Q v) (3 - p)) *
            (∑ R ∈ (Prepartition.splitCenter Q).boxes,
              volume.real (R : Set (Fin d → ℝ)) * (boxMean R v - boxMean Q v)) := by
        simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro R _
        ring
      _ = _ := by
        simp only [sum_volume_partition (Prepartition.splitCenter Q)
            (Prepartition.isPartition_splitCenter Q),
          sum_volume_mul_mean_sub (Prepartition.splitCenter Q)
            (Prepartition.isPartition_splitCenter Q) u hu,
          sum_volume_mul_mean_sub (Prepartition.splitCenter Q)
            (Prepartition.isPartition_splitCenter Q) v hv,
          mul_zero, sub_zero, add_zero]
  rw [integral_difference_square]
  calc
    _ ≤ ∑ R ∈ (Prepartition.splitCenter Q).boxes,
        (Real.rpow 2 ((d : ℝ) * (2 - p)) * ((3 - p) / (p - 1))) *
          (volume.real (R : Set (Fin d → ℝ)) *
            (scalarPsi p (boxMean R u) (boxMean R v) -
              scalarPsi p (boxMean Q u) (boxMean Q v) -
              2 * boxMean Q u * (boxMean R u - boxMean Q u) /
                Real.rpow (boxMean Q v) (2 - p) +
              (2 - p) * (boxMean Q u) ^ 2 * (boxMean R v - boxMean Q v) /
                Real.rpow (boxMean Q v) (3 - p))) := by
      apply Finset.sum_le_sum
      intro R hR
      convert mul_le_mul_of_nonneg_left (hpair R hR) (box_volume_pos R).le using 1 <;> ring
    _ = _ := by rw [← Finset.mul_sum, hcancel]

/-- Telescoping a scalar quantity on the finite cube tree. -/
private lemma sum_interior_child_sub [Nonempty (Fin d)]
    (I : Box (Fin d)) (N : ℕ) (f : Box (Fin d) → ℝ) :
    (∑ Q ∈ interior I N,
      ((∑ R ∈ (Prepartition.splitCenter Q).boxes, f R) - f Q)) =
      (∑ Q ∈ leaves I N, f Q) - f I := by
  rw [sum_interior]
  have hstep (n : ℕ) :
      (∑ Q ∈ (level I n).boxes,
        ((∑ R ∈ (Prepartition.splitCenter Q).boxes, f R) - f Q)) =
      (∑ Q ∈ (level I (n + 1)).boxes, f Q) - ∑ Q ∈ (level I n).boxes, f Q := by
    simp only [Finset.sum_sub_distrib, level_succ, Prepartition.biUnion,
      Prepartition.sum_biUnion_boxes]
  simp_rw [hstep]
  convert Finset.sum_range_sub (fun n : ℕ => ∑ Q ∈ (level I n).boxes, f Q) N using 1
  simp [leaves]

private lemma leaf_energy_sum (I : Box (Fin d)) (N : ℕ)
    (u v : (Fin d → ℝ) → ℝ) (p : ℝ)
    (hu : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, u x = u y)
    (hv : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, v x = v y) :
    (∑ Q ∈ leaves I N, volume.real (Q : Set (Fin d → ℝ)) *
      scalarPsi p (boxMean Q u) (boxMean Q v)) =
      ∫ x in (I : Set (Fin d → ℝ)), (u x) ^ 2 / Real.rpow (v x) (2 - p) := by
  rw [← sum_integral_partition (level I N) (level_isPartition I N)
    (fun x => (u x) ^ 2 / Real.rpow (v x) (2 - p)) (energy_integrable I N u v p hu hv)]
  apply Finset.sum_congr rfl
  intro Q hQ
  symm
  apply integral_eq_volume_mul
  intro x hx
  unfold scalarPsi
  rw [boxMean_of_constant Q u (hu Q hQ) hx, boxMean_of_constant Q v (hv Q hQ) hx]

/-- The weighted square estimate retains the paper's constant and permits signed `u`.
Constancy on the smallest cubes gives integrability; positivity of `v` gives
positive denominator averages. The top cube may be any positive-width box. -/
theorem weighted_square (d : ℕ) (hd : 0 < d)
    (I : Box (Fin d)) (N : ℕ) (u v : (Fin d → ℝ) → ℝ) (p : ℝ)
    (hp : 1 < p) (hp2 : p ≤ 2)
    (hu : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, u x = u y)
    (hv : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, v x = v y)
    (hvpos : ∀ x ∈ I, 0 < v x) :
    (∑ Q ∈ interior I N,
      ∫ x in (Q : Set (Fin d → ℝ)),
        (boxDifference Q u x) ^ 2 /
          Real.rpow ((∫ y in (Q : Set (Fin d → ℝ)), v y) /
            volume.real (Q : Set (Fin d → ℝ))) (2 - p)) ≤
      Real.rpow 2 ((d : ℝ) * (2 - p)) * ((3 - p) / (p - 1)) *
        ∫ x in (I : Set (Fin d → ℝ)), (u x) ^ 2 / Real.rpow (v x) (2 - p) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hui := integrableOn_of_leafConstant I N u hu
  have hvi := integrableOn_of_leafConstant I N v hv
  have hK : 0 ≤ Real.rpow 2 ((d : ℝ) * (2 - p)) * ((3 - p) / (p - 1)) :=
    mul_nonneg (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
      (div_nonneg (by linarith) (by linarith))
  have htop : 0 ≤ volume.real (I : Set (Fin d → ℝ)) *
      scalarPsi p (boxMean I u) (boxMean I v) := by
    apply mul_nonneg (box_volume_pos I).le
    unfold scalarPsi
    exact div_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos (boxMean_pos I v hvi hvpos) _).le
  change (∑ Q ∈ interior I N,
    ∫ x in (Q : Set (Fin d → ℝ)),
      (boxDifference Q u x) ^ 2 / Real.rpow (boxMean Q v) (2 - p)) ≤ _
  calc
    _ ≤ ∑ Q ∈ interior I N,
        (Real.rpow 2 ((d : ℝ) * (2 - p)) * ((3 - p) / (p - 1))) *
          ((∑ R ∈ (Prepartition.splitCenter Q).boxes,
              volume.real (R : Set (Fin d → ℝ)) *
                scalarPsi p (boxMean R u) (boxMean R v)) -
            volume.real (Q : Set (Fin d → ℝ)) *
              scalarPsi p (boxMean Q u) (boxMean Q v)) := by
      apply Finset.sum_le_sum
      intro Q hQ
      have hQI : (Q : Set (Fin d → ℝ)) ⊆ I :=
        le_of_mem_descendants (interior_subset_descendants I N hQ)
      exact weighted_parent_step Q u v p hp hp2 (hui.mono_set hQI) (hvi.mono_set hQI)
        (fun x hx => hvpos x (hQI hx))
    _ = (Real.rpow 2 ((d : ℝ) * (2 - p)) * ((3 - p) / (p - 1))) *
        ((∑ Q ∈ leaves I N, volume.real (Q : Set (Fin d → ℝ)) *
            scalarPsi p (boxMean Q u) (boxMean Q v)) -
          volume.real (I : Set (Fin d → ℝ)) * scalarPsi p (boxMean I u) (boxMean I v)) := by
      rw [← Finset.mul_sum, sum_interior_child_sub]
    _ = (Real.rpow 2 ((d : ℝ) * (2 - p)) * ((3 - p) / (p - 1))) *
        ((∫ x in (I : Set (Fin d → ℝ)), (u x) ^ 2 / Real.rpow (v x) (2 - p)) -
          volume.real (I : Set (Fin d → ℝ)) * scalarPsi p (boxMean I u) (boxMean I v)) := by
      rw [leaf_energy_sum I N u v p hu hv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sub_le_self _ htop) hK

end ReyZygmund
