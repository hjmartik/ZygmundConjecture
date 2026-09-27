import ReyZygmund.Geometry.FiniteAverages
import ReyZygmund.Geometry.FinitePartition
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.Tactic.Ring

/-! # The ordinary finite dyadic maximal function

Take the maximum of the Lebesgue averages of the absolute input over the retained
descendants, including the top cube and the smallest cubes.


-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry

variable {d : ℕ}

/-- The positive dyadic maximum through the retained final level. -/
noncomputable def finiteDyadicMaximal
    (I : Box (Fin d)) (N : ℕ) (g : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
    (fun n => ∑ Q ∈ (Geometry.level I n).boxes,
      Geometry.boxAverage Q (fun y => |g y|) x)

private theorem level_average_at {I Q : Box (Fin d)} {n : ℕ}
    (hQ : Q ∈ level I n) (g : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) (hx : x ∈ Q) :
    (∑ R ∈ (level I n).boxes, boxAverage R g x) =
      (∫ y in (Q : Set (Fin d → ℝ)), g y) / volume.real (Q : Set (Fin d → ℝ)) := by
  rw [Finset.sum_eq_single Q]
  · simp [boxAverage, hx]
  · intro R hR hRQ
    have hxR : x ∉ R := fun h => hRQ ((level I n).eq_of_mem_of_mem hR hQ h hx)
    simp [boxAverage, hxR]
  · simp [hQ]

private theorem level_average_eq_zero {I : Box (Fin d)} (n : ℕ)
    (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (hx : x ∉ I) :
    (∑ Q ∈ (level I n).boxes, boxAverage Q g x) = 0 := by
  apply Finset.sum_eq_zero
  intro Q hQ
  have hxQ : x ∉ Q := fun h => hx ((level I n).le_of_mem hQ h)
  simp [boxAverage, hxQ]

private theorem boxAverage_abs_nonneg (Q : Box (Fin d))
    (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    0 ≤ boxAverage Q (fun y => |g y|) x := by
  by_cases hx : x ∈ Q
  · simp only [boxAverage]
    rw [Set.indicator_of_mem (show x ∈ (Q : Set (Fin d → ℝ)) from hx)]
    exact div_nonneg (integral_nonneg (fun y => abs_nonneg (g y))) (box_volume_pos Q).le
  · simp [boxAverage, hx]

theorem finiteDyadicMaximal_nonneg (I : Box (Fin d)) (N : ℕ)
    (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    0 ≤ finiteDyadicMaximal I N g x := by
  apply Finset.le_sup'_of_le _ (Finset.mem_range.mpr (Nat.succ_pos N))
  exact Finset.sum_nonneg (fun Q _ => boxAverage_abs_nonneg Q g x)

theorem finiteDyadicMaximal_eq_zero_of_notMem (I : Box (Fin d)) (N : ℕ)
    (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (hx : x ∉ I) :
    finiteDyadicMaximal I N g x = 0 := by
  apply Finset.sup'_eq_of_forall
  intro n _
  exact level_average_eq_zero n (fun y => |g y|) x hx

theorem measurable_finiteDyadicMaximal (I : Box (Fin d)) (N : ℕ)
    (g : (Fin d → ℝ) → ℝ) : Measurable (finiteDyadicMaximal I N g) := by
  apply Finset.measurable_range_sup''
  intro n _
  exact Finset.measurable_sum _ (fun Q _ => measurable_const.indicator Q.measurableSet_coe)

/-- At a point of the top cube, each retained generation contributes the average on
its unique cube containing that point. -/
theorem lt_finiteDyadicMaximal_iff (I : Box (Fin d)) (N : ℕ)
    (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (hx : x ∈ I) (t : ℝ) :
    t < finiteDyadicMaximal I N g x ↔
      ∃ Q ∈ descendants I N, x ∈ Q ∧
        t < (∫ y in (Q : Set (Fin d → ℝ)), |g y|) /
          volume.real (Q : Set (Fin d → ℝ)) := by
  unfold finiteDyadicMaximal
  rw [Finset.lt_sup'_iff]
  constructor
  · rintro ⟨n, hn, htn⟩
    obtain ⟨Q, hQ, hxQ⟩ := level_isPartition I n x hx
    refine ⟨Q, mem_descendants.mpr
      ⟨n, Nat.lt_succ_iff.mp (Finset.mem_range.mp hn), hQ⟩, hxQ, ?_⟩
    rwa [level_average_at hQ (fun y => |g y|) x hxQ] at htn
  · rintro ⟨Q, hQ, hxQ, htQ⟩
    obtain ⟨n, hn, hQn⟩ := mem_descendants.mp hQ
    refine ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le hn), ?_⟩
    rwa [level_average_at hQn (fun y => |g y|) x hxQ]

private theorem containing_descendants_nonempty (I : Box (Fin d)) (N : ℕ)
    (x : Fin d → ℝ) (hx : x ∈ I) :
    ((descendants I N).filter (fun Q => x ∈ Q)).Nonempty := by
  refine ⟨I, Finset.mem_filter.mpr ⟨?_, hx⟩⟩
  exact mem_descendants.mpr ⟨0, Nat.zero_le N, Prepartition.mem_top.mpr rfl⟩

/-- Exact agreement with the finite maximum over containing descendants. -/
theorem finiteDyadicMaximal_eq_descendant_sup (I : Box (Fin d)) (N : ℕ)
    (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (hx : x ∈ I) :
    finiteDyadicMaximal I N g x =
      ((descendants I N).filter (fun Q => x ∈ Q)).sup'
        (containing_descendants_nonempty I N x hx)
        (fun Q => (∫ y in (Q : Set (Fin d → ℝ)), |g y|) /
          volume.real (Q : Set (Fin d → ℝ))) := by
  apply eq_of_forall_lt_iff
  intro t
  rw [lt_finiteDyadicMaximal_iff I N g x hx, Finset.lt_sup'_iff]
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨Q, hQ, hxQ, htQ⟩
    exact ⟨Q, ⟨hQ, hxQ⟩, htQ⟩
  · rintro ⟨Q, ⟨hQ, hxQ⟩, htQ⟩
    exact ⟨Q, hQ, hxQ, htQ⟩

/-- The output is constant on smallest cubes, without a constancy hypothesis
on the input. -/
theorem finiteDyadicMaximal_leafConstant (I : Box (Fin d)) (N : ℕ)
    (g : (Fin d → ℝ) → ℝ) :
    ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q,
      finiteDyadicMaximal I N g x = finiteDyadicMaximal I N g y := by
  intro Q hQ x hx y hy
  apply Finset.sup'_congr Finset.nonempty_range_add_one rfl
  intro n hn
  obtain ⟨R, hR, hQR⟩ :=
    level_refines I (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) hQ
  rw [level_average_at hR (fun z => |g z|) x (hQR hx),
    level_average_at hR (fun z => |g z|) y (hQR hy)]

theorem integrableOn_finiteDyadicMaximal (I : Box (Fin d)) (N : ℕ)
    (g : (Fin d → ℝ) → ℝ) :
    IntegrableOn (finiteDyadicMaximal I N g) (I : Set (Fin d → ℝ)) volume :=
  integrableOn_of_leafConstant I N _ (finiteDyadicMaximal_leafConstant I N g)

@[simp] theorem finiteDyadicMaximal_zero_depth (I : Box (Fin d))
    (g : (Fin d → ℝ) → ℝ) :
    finiteDyadicMaximal I 0 g = boxAverage I (fun y => |g y|) := by
  funext x
  simp [finiteDyadicMaximal]

theorem finiteDyadicMaximal_zero_depth_of_constant (I : Box (Fin d))
    (g : (Fin d → ℝ) → ℝ)
    (hg : ∀ x ∈ I, ∀ y ∈ I, g x = g y) :
    finiteDyadicMaximal I 0 g = (I : Set (Fin d → ℝ)).indicator (fun y => |g y|) := by
  rw [finiteDyadicMaximal_zero_depth]
  exact boxAverage_of_constant I (fun y => |g y|)
    (fun x hx y hy => congrArg abs (hg x hx y hy))

/-- The stopping-cube weak estimate requires only integrability on the top cube, not
constancy on the smallest cubes. -/
theorem finite_dyadic_maximal_weak (I : Box (Fin d)) (N : ℕ)
    (g : (Fin d → ℝ) → ℝ) (hg : IntegrableOn g (I : Set (Fin d → ℝ)) volume)
    (t : ℝ) (_ht : 0 < t) :
    t * volume.real {x ∈ (I : Set (Fin d → ℝ)) | t < finiteDyadicMaximal I N g x} ≤
      ∫ x in {x ∈ (I : Set (Fin d → ℝ)) | t < finiteDyadicMaximal I N g x}, |g x| := by
  let selected : Finset (Box (Fin d)) := (descendants I N).filter
    (fun Q => t < (∫ y in (Q : Set (Fin d → ℝ)), |g y|) /
      volume.real (Q : Set (Fin d → ℝ)))
  let stopping := maximalCubes selected
  have hstop : stopping ⊆ descendants I N := by
    intro Q hQ
    exact (Finset.mem_filter.mp (maximalCubes_subset selected hQ)).1
  have hdisj : Set.Pairwise (stopping : Set (Box (Fin d)))
      (fun P Q => Disjoint (P : Set (Fin d → ℝ)) (Q : Set (Fin d → ℝ))) := by
    intro P hP Q hQ hPQ
    have hPm := mem_maximalCubes.mp hP
    have hQm := mem_maximalCubes.mp hQ
    rcases descendants_nested_or_disjoint (hstop hP) (hstop hQ) with h | h | h
    · exact (hPQ (le_antisymm h (hPm.2 Q hQm.1 h))).elim
    · exact (hPQ (le_antisymm (hQm.2 P hPm.1 h) h)).elim
    · exact h
  have hset : {x ∈ (I : Set (Fin d → ℝ)) | t < finiteDyadicMaximal I N g x} =
      ⋃ Q ∈ stopping, (Q : Set (Fin d → ℝ)) := by
    ext x
    constructor
    · rintro ⟨hxI, htM⟩
      obtain ⟨Q, hQ, hxQ, htQ⟩ := (lt_finiteDyadicMaximal_iff I N g x hxI t).mp htM
      obtain ⟨P, hP, hQP⟩ := exists_maximal_supercube
        (show Q ∈ selected from Finset.mem_filter.mpr ⟨hQ, htQ⟩)
      exact Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hP, hQP hxQ⟩⟩
    · intro hx
      obtain ⟨Q, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hQ, hxQ⟩ := Set.mem_iUnion.mp hx
      have hxI : x ∈ I := le_of_mem_descendants (hstop hQ) hxQ
      refine ⟨hxI, (lt_finiteDyadicMaximal_iff I N g x hxI t).mpr
        ⟨Q, hstop hQ, hxQ, ?_⟩⟩
      exact (Finset.mem_filter.mp (maximalCubes_subset selected hQ)).2
  have habs : IntegrableOn (fun x => |g x|) (I : Set (Fin d → ℝ)) volume := by
    simpa only [IntegrableOn, Real.norm_eq_abs] using hg.norm
  have hint : ∀ Q ∈ stopping,
      IntegrableOn (fun x => |g x|) (Q : Set (Fin d → ℝ)) volume :=
    fun Q hQ => habs.mono_set (le_of_mem_descendants (hstop hQ))
  rw [hset, measureReal_biUnion_finset hdisj (fun Q _ => Q.measurableSet_coe)
    (fun Q _ => (Q.measure_coe_lt_top volume).ne),
    integral_biUnion_finset stopping (fun Q _ => Q.measurableSet_coe) hdisj hint,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro Q hQ
  have hmean := (Finset.mem_filter.mp (maximalCubes_subset selected hQ)).2
  exact ((lt_div_iff₀ (box_volume_pos Q)).mp hmean).le

private theorem weak_distribution_rpow {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) (f : α → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (p : ℝ) (hp : 1 < p)
    (hweak : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {x | t < f x} ≤ ν {x | t < f x}) :
    ENNReal.ofReal (p - 1) * (∫⁻ x, ENNReal.ofReal (f x ^ p) ∂μ) ≤
      ENNReal.ofReal p * (∫⁻ x, ENNReal.ofReal (f x ^ (p - 1)) ∂ν) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp1 : 0 < p - 1 := sub_pos.mpr hp
  have hmono :
      (∫⁻ t in Set.Ioi (0 : ℝ), μ {x | t < f x} * ENNReal.ofReal (t ^ (p - 1))) ≤
      ∫⁻ t in Set.Ioi (0 : ℝ), ν {x | t < f x} *
        ENNReal.ofReal (t ^ ((p - 1) - 1)) := by
    apply lintegral_mono_ae
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
      with t ht
    have ht0 : 0 < t := ht
    have hpow : t ^ (p - 1) = t * t ^ ((p - 1) - 1) := by
      calc
        t ^ (p - 1) = t ^ (1 + ((p - 1) - 1)) := by congr 1; ring
        _ = t ^ (1 : ℝ) * t ^ ((p - 1) - 1) := Real.rpow_add ht0 _ _
        _ = _ := by rw [Real.rpow_one]
    calc
      μ {x | t < f x} * ENNReal.ofReal (t ^ (p - 1)) =
          (ENNReal.ofReal t * μ {x | t < f x}) *
            ENNReal.ofReal (t ^ ((p - 1) - 1)) := by
        rw [hpow, ENNReal.ofReal_mul ht0.le]
        ac_rfl
      _ ≤ _ := mul_le_mul' (hweak t ht0) le_rfl
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ (ae_of_all μ hf0) hf.aemeasurable hp0,
    lintegral_rpow_eq_lintegral_meas_lt_mul ν (ae_of_all ν hf0) hf.aemeasurable hp1]
  calc
    _ = (ENNReal.ofReal p * ENNReal.ofReal (p - 1)) *
        (∫⁻ t in Set.Ioi (0 : ℝ), μ {x | t < f x} * ENNReal.ofReal (t ^ (p - 1))) := by
      ac_rfl
    _ ≤ (ENNReal.ofReal p * ENNReal.ofReal (p - 1)) *
        (∫⁻ t in Set.Ioi (0 : ℝ), ν {x | t < f x} *
          ENNReal.ofReal (t ^ ((p - 1) - 1))) := mul_le_mul' le_rfl hmono
    _ = _ := by ac_rfl

private theorem integral_moment_of_weak {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f g : α → ℝ)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hg : Integrable g μ) (hg0 : ∀ x, 0 ≤ g x)
    (p : ℝ) (hp : 1 < p)
    (hfp : Integrable (fun x => f x ^ p) μ)
    (hgp : Integrable (fun x => g x * f x ^ (p - 1)) μ)
    (hweak : ∀ t : ℝ, 0 < t →
      t * μ.real {x | t < f x} ≤ ∫ x in {x | t < f x}, g x ∂μ) :
    (p - 1) * (∫ x, f x ^ p ∂μ) ≤ p * (∫ x, g x * f x ^ (p - 1) ∂μ) := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (g x))
  have hweak' : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {x | t < f x} ≤ ν {x | t < f x} := by
    intro t ht
    have hs : MeasurableSet {x | t < f x} := measurableSet_lt measurable_const hf
    have h := ENNReal.ofReal_le_ofReal (hweak t ht)
    rw [ENNReal.ofReal_mul ht.le, ofReal_measureReal (measure_ne_top μ _),
      ofReal_integral_eq_lintegral_ofReal hg.restrict (ae_of_all _ hg0)] at h
    simpa only [ν, withDensity_apply _ hs] using h
  have h := weak_distribution_rpow μ ν f hf hf0 p hp hweak'
  have hright : (∫⁻ x, ENNReal.ofReal (f x ^ (p - 1)) ∂ν) =
      ENNReal.ofReal (∫ x, g x * f x ^ (p - 1) ∂μ) := by
    rw [lintegral_withDensity_eq_lintegral_mul₀ hg.aemeasurable.ennreal_ofReal
      (hf.pow_const (p - 1)).ennreal_ofReal.aemeasurable]
    rw [ofReal_integral_eq_lintegral_ofReal hgp
      (ae_of_all _ (fun x => mul_nonneg (hg0 x) (Real.rpow_nonneg (hf0 x) _)))]
    apply lintegral_congr
    intro x
    exact (ENNReal.ofReal_mul (hg0 x)).symm
  rw [← ofReal_integral_eq_lintegral_ofReal hfp
    (ae_of_all _ (fun x => Real.rpow_nonneg (hf0 x) _)), hright,
    ← ENNReal.ofReal_mul (sub_pos.mpr hp).le,
    ← ENNReal.ofReal_mul (lt_trans zero_lt_one hp).le] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (lt_trans zero_lt_one hp).le
      (integral_nonneg (fun x => mul_nonneg (hg0 x) (Real.rpow_nonneg (hf0 x) _))))).mp h

private theorem finite_dyadic_maximal_moment (I : Box (Fin d)) (N : ℕ)
    (g : (Fin d → ℝ) → ℝ) (p : ℝ) (hp : 1 < p)
    (hg : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y) :
    (p - 1) * (∫ x in (I : Set (Fin d → ℝ)), finiteDyadicMaximal I N g x ^ p) ≤
      p * (∫ x in (I : Set (Fin d → ℝ)),
        |g x| * finiteDyadicMaximal I N g x ^ (p - 1)) := by
  let μ := volume.restrict (I : Set (Fin d → ℝ))
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (I.measure_coe_lt_top volume).ne
  have hM := finiteDyadicMaximal_leafConstant I N g
  have hgi : IntegrableOn g (I : Set (Fin d → ℝ)) volume :=
    integrableOn_of_leafConstant I N g hg
  apply integral_moment_of_weak μ (finiteDyadicMaximal I N g) (fun x => |g x|)
    (measurable_finiteDyadicMaximal I N g) (finiteDyadicMaximal_nonneg I N g)
    (by simpa only [Real.norm_eq_abs] using hgi.norm) (fun x => abs_nonneg (g x)) p hp
  · exact integrableOn_of_leafConstant I N _
      (fun Q hQ x hx y hy => congrArg (fun z : ℝ => z ^ p) (hM Q hQ x hx y hy))
  · apply integrableOn_of_leafConstant I N
    intro Q hQ x hx y hy
    rw [hg Q hQ x hx y hy, hM Q hQ x hx y hy]
  · intro t ht
    have hs : MeasurableSet {x | t < finiteDyadicMaximal I N g x} :=
      measurableSet_lt measurable_const (measurable_finiteDyadicMaximal I N g)
    have hset : {x | t < finiteDyadicMaximal I N g x} ∩ (I : Set (Fin d → ℝ)) =
        {x ∈ (I : Set (Fin d → ℝ)) | t < finiteDyadicMaximal I N g x} := by
      ext x
      exact and_comm
    simpa only [μ, measureReal_def, Measure.restrict_apply hs,
      Measure.restrict_restrict hs, hset] using finite_dyadic_maximal_weak I N g hgi t ht

private theorem memLp_of_leafConstant (I : Box (Fin d)) (N : ℕ)
    (g : (Fin d → ℝ) → ℝ) (r : ℝ) (hr : 0 < r)
    (hg : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y) :
    MemLp g (ENNReal.ofReal r) (volume.restrict (I : Set (Fin d → ℝ))) := by
  apply (integrable_norm_rpow_iff
    (integrableOn_of_leafConstant I N g hg).aestronglyMeasurable
    (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top).mp
  apply integrableOn_of_leafConstant I N
  intro Q hQ x hx y hy
  rw [hg Q hQ x hx y hy]

private theorem finite_dyadic_maximal_holder (I : Box (Fin d)) (N : ℕ)
    (g : (Fin d → ℝ) → ℝ) (p : ℝ) (hp : 1 < p)
    (hg : ∀ Q ∈ leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y) :
    (∫ x in (I : Set (Fin d → ℝ)), |g x| * finiteDyadicMaximal I N g x ^ (p - 1)) ≤
      (∫ x in (I : Set (Fin d → ℝ)), |g x| ^ p) ^ (1 / p) *
        (∫ x in (I : Set (Fin d → ℝ)), finiteDyadicMaximal I N g x ^ p) ^
          (1 / Real.conjExponent p) := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have hM := finiteDyadicMaximal_leafConstant I N g
  have hgLp := memLp_of_leafConstant I N (fun x => |g x|) p (lt_trans zero_lt_one hp)
    (fun Q hQ x hx y hy => congrArg abs (hg Q hQ x hx y hy))
  have hMLp := memLp_of_leafConstant I N (fun x => finiteDyadicMaximal I N g x ^ (p - 1))
    (Real.conjExponent p) hpq.symm.pos
    (fun Q hQ x hx y hy => congrArg (fun z : ℝ => z ^ (p - 1)) (hM Q hQ x hx y hy))
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (ae_of_all _ (fun x => abs_nonneg (g x)))
    (ae_of_all _ (fun x => Real.rpow_nonneg (finiteDyadicMaximal_nonneg I N g x) (p - 1)))
    hgLp hMLp
  have hpowers (x : Fin d → ℝ) :
      (finiteDyadicMaximal I N g x ^ (p - 1)) ^ Real.conjExponent p =
        finiteDyadicMaximal I N g x ^ p := by
    rw [← Real.rpow_mul (finiteDyadicMaximal_nonneg I N g x), hpq.sub_one_mul_conj]
  simpa only [hpowers] using h

private theorem rpow_bound_of_moment (A B p : ℝ) (hp : 1 < p)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : (p - 1) * A ≤ p * (B ^ (1 / p) * A ^ (1 / Real.conjExponent p))) :
    A ^ (1 / p) ≤ (p / (p - 1)) * B ^ (1 / p) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp1 : 0 < p - 1 := sub_pos.mpr hp
  by_cases hA0 : A = 0
  · subst A
    rw [Real.zero_rpow (ne_of_gt (one_div_pos.mpr hp0))]
    exact mul_nonneg (div_nonneg hp0.le hp1.le) (Real.rpow_nonneg hB _)
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    have hconj : 1 / p + 1 / Real.conjExponent p = 1 := by
      simpa only [one_div] using (Real.HolderConjugate.conjExponent hp).inv_add_inv_eq_one
    have hdecomp : A ^ (1 / p) * A ^ (1 / Real.conjExponent p) = A := by
      rw [← Real.rpow_add hApos, hconj, Real.rpow_one]
    have hproduct : ((p - 1) * A ^ (1 / p)) * A ^ (1 / Real.conjExponent p) ≤
        (p * B ^ (1 / p)) * A ^ (1 / Real.conjExponent p) := by
      calc
        _ = (p - 1) * A := by rw [mul_assoc, hdecomp]
        _ ≤ p * (B ^ (1 / p) * A ^ (1 / Real.conjExponent p)) := h
        _ = _ := by ring
    have hcancel : (p - 1) * A ^ (1 / p) ≤ p * B ^ (1 / p) :=
      le_of_mul_le_mul_right hproduct (Real.rpow_pos_of_pos hApos _)
    calc
      A ^ (1 / p) ≤ (p * B ^ (1 / p)) / (p - 1) := (le_div_iff₀' hp1).mpr hcancel
      _ = (p / (p - 1)) * B ^ (1 / p) := by ring

/-- The ordinary finite one-coordinate maximal estimate, with the paper's coefficient
for each real `p > 1`. Hypotheses on the input concern only the top cube. -/
theorem finite_dyadic_maximal_lp (d : ℕ) (_hd : 0 < d)
    (I : Box (Fin d)) (N : ℕ) (g : (Fin d → ℝ) → ℝ)
    (p : ℝ) (hp : 1 < p)
    (hg : ∀ Q ∈ Geometry.leaves I N, ∀ x ∈ Q, ∀ y ∈ Q, g x = g y) :
    Real.rpow
      (∫ x in (I : Set (Fin d → ℝ)), Real.rpow (finiteDyadicMaximal I N g x) p) (1 / p) ≤
      (p / (p - 1)) * Real.rpow
        (∫ x in (I : Set (Fin d → ℝ)), Real.rpow |g x| p) (1 / p) := by
  change (∫ x in (I : Set (Fin d → ℝ)), finiteDyadicMaximal I N g x ^ p) ^ (1 / p) ≤
    (p / (p - 1)) * (∫ x in (I : Set (Fin d → ℝ)), |g x| ^ p) ^ (1 / p)
  apply rpow_bound_of_moment _ _ p hp
  · exact integral_nonneg (fun x => Real.rpow_nonneg (finiteDyadicMaximal_nonneg I N g x) p)
  · exact integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg (g x)) p)
  · exact (finite_dyadic_maximal_moment I N g p hp hg).trans
      (mul_le_mul_of_nonneg_left (finite_dyadic_maximal_holder I N g p hp hg)
        (lt_trans zero_lt_one hp).le)

end ReyZygmund
