import ReyZygmund.Weighted.Averaging
import ReyZygmund.Geometry.FiniteCrossAverage

/-! # A weighted square estimate for cross-coordinate averages

Apply the weighted averaging inequality on each partition cube. Constancy on the
smallest cubes gives integrability, including for the quotients. Summing over the
partition gives the integral estimate on the top cube.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry

variable {d : ℕ}

private theorem leafConstant_on_descendant
    (I : Box (Fin d)) (N : ℕ) (g : (Fin d → ℝ) → ℝ)
    (hg : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y)
    (P : Box (Fin d)) (n : ℕ) (hn : n ≤ N) (hP : P ∈ level I n) :
    ∀ Q ∈ leaves P (N - n), ∀ x ∈ Q, ∀ y ∈ Q, g x = g y := by
  intro Q hQ
  rw [leaves_localization hP hn] at hQ
  exact hg Q (Finset.mem_filter.mp hQ).1

/-- The denominator is strictly positive at every point of the top cube. Values of the
input outside that cube are unrestricted. -/
theorem finiteCrossAverage_pos
    (I : Box (Fin d)) (N : ℕ) (eligible : Finset (Box (Fin d)))
    (he : eligible ⊆ descendants I N) (v : (Fin d → ℝ) → ℝ)
    (hv : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, v x = v y)
    (hvpos : ∀ x ∈ I, 0 < v x) (x : Fin d → ℝ) (hx : x ∈ I) :
    0 < finiteCrossAverage I N eligible v x := by
  obtain ⟨P, hP, hxP⟩ := maximalPartition_isPartition I N eligible he x hx
  have hPI := le_of_mem_descendants (partitionCubes_subset_descendants he hP)
  have hvi := (integrableOn_of_leafConstant I N v hv).mono_set hPI
  have hnonneg : 0 ≤ᵐ[volume.restrict (P : Set (Fin d → ℝ))] v := by
    filter_upwards [self_mem_ae_restrict P.measurableSet_coe] with y hy
    exact (hvpos y (hPI hy)).le
  have hsupp : Function.support v ∩ (P : Set (Fin d → ℝ)) = (P : Set (Fin d → ℝ)) := by
    apply Set.inter_eq_right.mpr
    intro y hy
    exact ne_of_gt (hvpos y (hPI hy))
  rw [finiteCrossAverage_eq_on_partition he v hP hxP]
  apply div_pos _ (box_volume_pos P)
  apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hvi).mpr
  rw [hsupp, ← ofReal_measureReal (P.measure_coe_lt_top volume).ne]
  exact ENNReal.ofReal_pos.mpr (box_volume_pos P)

/-- The normalized weighted square inequality on the cross partition. -/
theorem finiteCrossAverage_weighted_square
    (I : Box (Fin d)) (N : ℕ) (eligible : Finset (Box (Fin d)))
    (he : eligible ⊆ descendants I N) (u v : (Fin d → ℝ) → ℝ)
    (hu : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, u x = u y)
    (hv : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, v x = v y)
    (hvpos : ∀ x ∈ I, 0 < v x) (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2)
    (x : Fin d → ℝ) (hx : x ∈ I) :
    (finiteCrossAverage I N eligible u x) ^ 2 /
        Real.rpow (finiteCrossAverage I N eligible v x) (2 - p) ≤
      finiteCrossAverage I N eligible (fun y => (u y) ^ 2 / Real.rpow (v y) (2 - p)) x := by
  obtain ⟨P, hP, hxP⟩ := maximalPartition_isPartition I N eligible he x hx
  obtain ⟨n, hn, hPn⟩ := mem_descendants.mp (partitionCubes_subset_descendants he hP)
  have h := box_average_weighted_square P (N - n) u v p hp hp2
    (leafConstant_on_descendant I N u hu P n hn hPn)
    (leafConstant_on_descendant I N v hv P n hn hPn)
    (fun y hy => hvpos y ((level I n).le_of_mem hPn hy))
  rw [finiteCrossAverage_eq_on_partition he u hP hxP,
    finiteCrossAverage_eq_on_partition he v hP hxP,
    finiteCrossAverage_eq_on_partition he
      (fun y => (u y) ^ 2 / Real.rpow (v y) (2 - p)) hP hxP]
  exact h

/-- Cross-coordinate averaging contracts the integrated weighted square. All functions
compared are integrable on the top cube. -/
theorem finiteCrossAverage_weighted_square_integral
    (I : Box (Fin d)) (N : ℕ) (eligible : Finset (Box (Fin d)))
    (he : eligible ⊆ descendants I N) (u v : (Fin d → ℝ) → ℝ)
    (hu : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, u x = u y)
    (hv : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, v x = v y)
    (hvpos : ∀ x ∈ I, 0 < v x) (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
    (∫ x in (I : Set (Fin d → ℝ)),
        (finiteCrossAverage I N eligible u x) ^ 2 /
          Real.rpow (finiteCrossAverage I N eligible v x) (2 - p)) ≤
      ∫ x in (I : Set (Fin d → ℝ)), (u x) ^ 2 / Real.rpow (v x) (2 - p) := by
  let g := fun x => (u x) ^ 2 / Real.rpow (v x) (2 - p)
  have hg : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y := by
    intro Q hQ x hx y hy
    dsimp [g]
    rw [hu Q hQ x hx y hy, hv Q hQ x hx y hy]
  have hleft : IntegrableOn
      (fun x => (finiteCrossAverage I N eligible u x) ^ 2 /
        Real.rpow (finiteCrossAverage I N eligible v x) (2 - p))
      (I : Set (Fin d → ℝ)) volume := by
    apply integrableOn_of_leafConstant I N
    intro Q hQ x hx y hy
    rw [finiteCrossAverage_leafConstant he u Q hQ x hx y hy,
      finiteCrossAverage_leafConstant he v Q hQ x hx y hy]
  have hright : IntegrableOn (finiteCrossAverage I N eligible g)
      (I : Set (Fin d → ℝ)) volume :=
    (finiteCrossAverage_integrable I N eligible g).integrableOn
  have hind : (I : Set (Fin d → ℝ)).indicator (finiteCrossAverage I N eligible g) =
      finiteCrossAverage I N eligible g := by
    funext x
    by_cases hx : x ∈ I
    · exact Set.indicator_of_mem hx _
    · rw [Set.indicator_of_notMem hx, finiteCrossAverage_eq_zero_of_notMem he g hx]
  calc
    _ ≤ ∫ x in (I : Set (Fin d → ℝ)), finiteCrossAverage I N eligible g x :=
      setIntegral_mono_on hleft hright I.measurableSet_coe
        (fun x hx => finiteCrossAverage_weighted_square I N eligible he u v hu hv hvpos p hp hp2 x hx)
    _ = ∫ x, finiteCrossAverage I N eligible g x := by
      rw [← integral_indicator I.measurableSet_coe, hind]
    _ = _ := finiteCrossAverage_integral he g (integrableOn_of_leafConstant I N g hg)

end ReyZygmund
