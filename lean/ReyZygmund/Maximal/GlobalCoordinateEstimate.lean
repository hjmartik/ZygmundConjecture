import ReyZygmund.Maximal.GlobalCoordinate
import ReyZygmund.Maximal.OrdinaryGlobal
import Mathlib.MeasureTheory.Measure.Prod

/-! # Full-grid coordinate estimates and almost-everywhere equality

The coordinate operators are extended-valued. Product integration shows that an
almost-everywhere change of input preserves their values almost everywhere;
equality need not hold on every fixed slice. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

private theorem ae_coordinate_update_congr (j : Fin m)
    (F G : ProductPoint d → ℝ≥0∞) (hFG : F =ᵐ[volume] G) :
    ∀ᵐ x ∂volume, (fun y => F (Function.update x j y)) =ᵐ[volume]
      (fun y => G (Function.update x j y)) := by
  cases m with
  | zero => exact Fin.elim0 j
  | succ n =>
      let e : ProductPoint d ≃ᵐ
          ((∀ i : Fin n, Fin (d (j.succAbove i)) → ℝ) × (Fin (d j) → ℝ)) :=
        (MeasurableEquiv.piFinSuccAbove (fun i => Fin (d i) → ℝ) j).trans
          MeasurableEquiv.prodComm
      have he : MeasurePreserving e volume (volume.prod volume) :=
        Measure.measurePreserving_swap.comp
          (volume_preserving_piFinSuccAbove (fun i => Fin (d i) → ℝ) j)
      have hprod : (fun z => F (e.symm z)) =ᵐ[volume.prod volume]
          (fun z => G (e.symm z)) :=
        (he.symm e).quasiMeasurePreserving.ae_eq_comp hFG
      have hslice := Measure.ae_ae_of_ae_prod hprod
      have hreturn :=
        (Measure.quasiMeasurePreserving_fst.comp he.quasiMeasurePreserving).ae hslice
      filter_upwards [hreturn] with x hx
      change (fun y => F (j.insertNth y (j.removeNth x))) =ᵐ[volume]
        (fun y => G (j.insertNth y (j.removeNth x))) at hx
      simpa only [Fin.insertNth_removeNth] using hx

theorem coordinateGridMaximal_ae_congr (D : ∀ i, DyadicGrid (d i)) (j : Fin m)
    (F G : ProductPoint d → ℝ≥0∞) (hFG : F =ᵐ[volume] G) :
    coordinateGridMaximal D j F =ᵐ[volume] coordinateGridMaximal D j G := by
  filter_upwards [ae_coordinate_update_congr j F G hFG] with x hx
  apply iSup_congr
  intro Q
  by_cases hQ : x j ∈ Q.1
  · rw [coordinateGridAverage_of_mem j Q.1 F x hQ,
      coordinateGridAverage_of_mem j Q.1 G x hQ]
    congr 1
    exact lintegral_congr_ae (ae_restrict_of_ae hx)
  · rw [coordinateGridAverage_of_notMem j Q.1 F x hQ,
      coordinateGridAverage_of_notMem j Q.1 G x hQ]

theorem aemeasurable_coordinateGridMaximal (D : ∀ i, DyadicGrid (d i)) (j : Fin m)
    (F : ProductPoint d → ℝ≥0∞) (hF : AEMeasurable F volume) :
    AEMeasurable (coordinateGridMaximal D j F) volume := by
  exact (measurable_coordinateGridMaximal D j (hF.mk F) hF.measurable_mk).aemeasurable.congr
    (coordinateGridMaximal_ae_congr D j F (hF.mk F) hF.ae_eq_mk).symm

theorem foldr_coordinateGridMaximal_ae_congr
    (D : ∀ i, DyadicGrid (d i)) (order : List (Fin m))
    (F G : ProductPoint d → ℝ≥0∞) (hFG : F =ᵐ[volume] G) :
    order.foldr (fun j H => coordinateGridMaximal D j H) F =ᵐ[volume]
      order.foldr (fun j H => coordinateGridMaximal D j H) G := by
  induction order with
  | nil => exact hFG
  | cons j order ih => exact coordinateGridMaximal_ae_congr D j _ _ ih

theorem iteratedGridMaximal_ae_congr (D : ∀ i, DyadicGrid (d i))
    (F G : ProductPoint d → ℝ≥0∞) (hFG : F =ᵐ[volume] G) :
    iteratedGridMaximal D F =ᵐ[volume] iteratedGridMaximal D G :=
  foldr_coordinateGridMaximal_ae_congr D (List.finRange m) F G hFG

theorem aemeasurable_iteratedGridMaximal (D : ∀ i, DyadicGrid (d i))
    (F : ProductPoint d → ℝ≥0∞) (hF : AEMeasurable F volume) :
    AEMeasurable (iteratedGridMaximal D F) volume := by
  exact (measurable_iteratedGridMaximal D (hF.mk F) hF.measurable_mk).aemeasurable.congr
    (iteratedGridMaximal_ae_congr D F (hF.mk F) hF.ae_eq_mk).symm

private theorem memLp_toReal_of_power_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (F : α → ℝ≥0∞) (hF : AEMeasurable F μ)
    (p : ℝ) (hp : 0 < p) (hint : (∫⁻ x, (F x) ^ p ∂μ) < ∞) :
    MemLp (fun x => (F x).toReal) (ENNReal.ofReal p) μ := by
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
    hF.ennreal_toReal.aestronglyMeasurable).mpr
  rw [ENNReal.toReal_ofReal hp.le]
  apply lt_of_le_of_lt _ hint
  apply lintegral_mono
  intro x
  dsimp only
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.rpow_le_rpow ENNReal.ofReal_toReal_le hp.le

private theorem ofReal_boxMean_eq_lintegral {q : ℕ} (Q : Box (Fin q))
    (g : (Fin q → ℝ) → ℝ) (hg : IntegrableOn g (Q : Set (Fin q → ℝ)) volume)
    (H : (Fin q → ℝ) → ℝ≥0∞) (hH : (fun x => ENNReal.ofReal |g x|) =ᵐ[volume] H) :
    ENNReal.ofReal ((∫ y in (Q : Set (Fin q → ℝ)), |g y|) /
      volume.real (Q : Set (Fin q → ℝ))) =
        (volume (Q : Set (Fin q → ℝ)))⁻¹ * ∫⁻ y in (Q : Set (Fin q → ℝ)), H y := by
  have hi := ofReal_integral_eq_lintegral_ofReal hg.abs
    (Filter.Eventually.of_forall (fun x => abs_nonneg (g x)))
  rw [ENNReal.ofReal_div_of_pos (box_volume_pos Q), measureReal_def,
    ENNReal.ofReal_toReal (Q.measure_coe_lt_top volume).ne, hi,
    div_eq_mul_inv, mul_comm]
  exact congrArg ((volume (Q : Set (Fin q → ℝ)))⁻¹ * ·)
    (lintegral_congr_ae (ae_restrict_of_ae hH))

private theorem oneBlock_productBox {q : ℕ} (Q : Box (Fin q)) :
    productBox (fun _ : Fin 1 => Q) =
      (MeasurableEquiv.piUnique (fun _ : Fin 1 => Fin q → ℝ)) ⁻¹'
        (Q : Set (Fin q → ℝ)) := by
  ext z
  rw [mem_productBox]
  change (∀ i : Fin 1, z i ∈ Q) ↔ z default ∈ Q
  constructor
  · exact fun h => h default
  · intro h i
    have hi : i = (default : Fin 1) := Subsingleton.elim _ _
    subst i
    exact h

private theorem cubeGridMaximal_power_integral {q : ℕ} (D : DyadicGrid q)
    (hq : 0 < q) (H : (Fin q → ℝ) → ℝ≥0∞) (hH : Measurable H)
    (p : ℝ) (hp : 1 < p) :
    (∫⁻ x, (⨆ Q : {Q : Box (Fin q) | ∃ n : ℤ, Q ∈ D.cubes n},
      (Q.1 : Set (Fin q → ℝ)).indicator
        (fun _ => (volume (Q.1 : Set (Fin q → ℝ)))⁻¹ *
          ∫⁻ y in (Q.1 : Set (Fin q → ℝ)), H y) x) ^ p) ≤
      (ENNReal.ofReal (p / (p - 1))) ^ p * ∫⁻ x, (H x) ^ p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hp' : 0 < p / (p - 1) := div_pos hp0 (sub_pos.mpr hp)
  by_cases ht : (∫⁻ x, (H x) ^ p) = ∞
  · rw [ht, ENNReal.mul_top
      (ENNReal.rpow_pos_of_nonneg (ENNReal.ofReal_pos.mpr hp') hp0.le).ne']
    exact le_top
  have hint : (∫⁻ x, (H x) ^ p) < ∞ := lt_top_iff_ne_top.mpr ht
  let g : (Fin q → ℝ) → ℝ := fun x => (H x).toReal
  have hg : MemLp g (ENNReal.ofReal p) volume :=
    memLp_toReal_of_power_integral volume H hH.aemeasurable p hp0 hint
  have hfinite : ∀ᵐ x ∂volume, H x ≠ ∞ := by
    filter_upwards [ae_lt_top (hH.pow_const p) ht] with x hx
    exact ((ENNReal.rpow_lt_top_iff_of_pos hp0).mp hx).ne
  have hreal : (fun x => ENNReal.ofReal |g x|) =ᵐ[volume] H := by
    filter_upwards [hfinite] with x hx
    exact (congrArg ENNReal.ofReal (abs_of_nonneg (ENNReal.toReal_nonneg))).trans
      (ENNReal.ofReal_toReal hx)
  let e : ProductPoint (fun _ : Fin 1 => q) ≃ᵐ (Fin q → ℝ) :=
    MeasurableEquiv.piUnique (fun _ : Fin 1 => Fin q → ℝ)
  have he : MeasurePreserving e := volume_preserving_piUnique _
  let D1 : ∀ _ : Fin 1, DyadicGrid q := fun _ => D
  let g1 : ProductPoint (fun _ : Fin 1 => q) → ℝ := fun z => g (e z)
  have hg1 : MemLp g1 (ENNReal.ofReal p) volume := hg.comp_measurePreserving he
  have hin : (∫⁻ z, (ENNReal.ofReal |g1 z|) ^ p) = ∫⁻ x, (H x) ^ p := by
    calc
      _ = ∫⁻ x, (ENNReal.ofReal |g x|) ^ p :=
        he.lintegral_comp_emb e.measurableEmbedding _
      _ = _ := lintegral_congr_ae (hreal.fun_comp (fun t => t ^ p))
  have hpoint (x : Fin q → ℝ) :
      (⨆ Q : {Q : Box (Fin q) | ∃ n : ℤ, Q ∈ D.cubes n},
        (Q.1 : Set (Fin q → ℝ)).indicator
          (fun _ => (volume (Q.1 : Set (Fin q → ℝ)))⁻¹ *
            ∫⁻ y in (Q.1 : Set (Fin q → ℝ)), H y) x) ≤
      familyMaximal (gridRectangles D1) g1 (e.symm x) := by
    apply iSup_le
    intro Q
    by_cases hx : x ∈ Q.1
    · rw [Set.indicator_of_mem hx]
      let R : ∀ _ : Fin 1, Box (Fin q) := fun _ => Q.1
      have hR : R ∈ gridRectangles D1 := fun _ => Q.property
      have hset : productBox R = e ⁻¹' (Q.1 : Set (Fin q → ℝ)) :=
        oneBlock_productBox Q.1
      have hxR : e.symm x ∈ productBox R := by
        rw [hset]
        exact (e.apply_symm_apply x).symm ▸ hx
      have hvol : volume.real (productBox R) =
          volume.real (Q.1 : Set (Fin q → ℝ)) := by
        rw [measureReal_def, measureReal_def, hset, he.measure_preimage_equiv]
      have hi : (∫ z in productBox R, |g1 z|) =
          ∫ y in (Q.1 : Set (Fin q → ℝ)), |g y| := by
        rw [hset]
        exact (he.restrict_preimage Q.1.measurableSet_coe).integral_comp' (fun y => |g y|)
      have hgQ : IntegrableOn g (Q.1 : Set (Fin q → ℝ)) volume := by
        let : IsFiniteMeasure (volume.restrict (Q.1 : Set (Fin q → ℝ))) :=
          isFiniteMeasure_restrict.mpr (Q.1.measure_coe_lt_top volume).ne
        apply MemLp.integrable _ (hg.restrict (Q.1 : Set (Fin q → ℝ)))
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
      have hmean : ENNReal.ofReal ((∫ z in productBox R, |g1 z|) /
          volume.real (productBox R)) =
          (volume (Q.1 : Set (Fin q → ℝ)))⁻¹ *
            ∫⁻ y in (Q.1 : Set (Fin q → ℝ)), H y := by
        rw [hi, hvol]
        exact ofReal_boxMean_eq_lintegral Q.1 g hgQ H hreal
      have hsel := le_iSup (fun S : gridRectangles D1 =>
        ENNReal.ofReal ((productBox S.1).indicator
          (fun _ => (∫ y in productBox S.1, |g1 y|) /
            volume.real (productBox S.1)) (e.symm x))) ⟨R, hR⟩
      rw [Set.indicator_of_mem hxR, hmean] at hsel
      exact hsel
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  calc
    _ ≤ ∫⁻ x, (familyMaximal (gridRectangles D1) g1 (e.symm x)) ^ p :=
      lintegral_mono (fun x => ENNReal.rpow_le_rpow (hpoint x) hp0.le)
    _ = ∫⁻ z, (familyMaximal (gridRectangles D1) g1 z) ^ p :=
      (he.symm e).lintegral_comp_emb e.symm.measurableEmbedding
        (fun z : ProductPoint (fun _ : Fin 1 => q) =>
          (familyMaximal (gridRectangles D1) g1 z) ^ p)
    _ ≤ (ENNReal.ofReal (p / (p - 1))) ^ p *
        ∫⁻ z, (ENNReal.ofReal |g1 z|) ^ p := by
      simpa only [pow_one] using ordinary_grid_family_maximal_lintegral
        (fun _ : Fin 1 => hq) D1 (gridRectangles D1) (fun _ h => h) g1 p hp hg1
    _ = _ := congrArg ((ENNReal.ofReal (p / (p - 1))) ^ p * ·) hin

/-- The whole-grid coordinate operator has the one-coordinate
power-integral bound. Both sides may be infinite. -/
theorem coordinateGridMaximal_power_integral (D : ∀ i, DyadicGrid (d i))
    (j : Fin m) (hd : 0 < d j) (F : ProductPoint d → ℝ≥0∞)
    (hF : Measurable F) (p : ℝ) (hp : 1 < p) :
    (∫⁻ x, (coordinateGridMaximal D j F x) ^ p) ≤
      (ENNReal.ofReal (p / (p - 1))) ^ p * ∫⁻ x, (F x) ^ p := by
  let C : ℝ≥0∞ := (ENNReal.ofReal (p / (p - 1))) ^ p
  have hslice :
      lmarginal (fun _ => volume) {j} (fun x => (coordinateGridMaximal D j F x) ^ p) ≤
        lmarginal (fun _ => volume) {j} (fun x => C * (F x) ^ p) := by
    intro x
    simp only [lmarginal_singleton]
    have hxF : Measurable (fun y : Fin (d j) → ℝ => F (Function.update x j y)) :=
      hF.comp (measurable_update x (a := j))
    rw [lintegral_const_mul (μ := (volume : Measure (Fin (d j) → ℝ))) C
      (hxF.pow_const p)]
    simpa only [coordinateGridMaximal_update] using
      cubeGridMaximal_power_integral (D j) hd
        (fun y => F (Function.update x j y)) hxF p hp
  calc
    _ ≤ ∫⁻ x, C * (F x) ^ p :=
      lintegral_le_of_lmarginal_le {j}
        ((measurable_coordinateGridMaximal D j F hF).pow_const p)
        ((hF.pow_const p).const_mul C) hslice
    _ = _ := lintegral_const_mul C (hF.pow_const p)

private theorem foldr_coordinateGridMaximal_power_integral
    (D : ∀ i, DyadicGrid (d i)) (hd : ∀ i, 0 < d i)
    (F : ProductPoint d → ℝ≥0∞) (hF : Measurable F) (p : ℝ) (hp : 1 < p)
    (order : List (Fin m)) :
    (∫⁻ x, (order.foldr (fun j G => coordinateGridMaximal D j G) F x) ^ p) ≤
      ((ENNReal.ofReal (p / (p - 1))) ^ p) ^ order.length * ∫⁻ x, (F x) ^ p := by
  let C : ℝ≥0∞ := (ENNReal.ofReal (p / (p - 1))) ^ p
  induction order with
  | nil => simp
  | cons j order ih =>
      calc
        _ ≤ C * ∫⁻ x,
            (order.foldr (fun i G => coordinateGridMaximal D i G) F x) ^ p :=
          coordinateGridMaximal_power_integral D j (hd j) _
            (measurable_foldr_coordinateGridMaximal D order F hF) p hp
        _ ≤ C * (C ^ order.length * ∫⁻ x, (F x) ^ p) := mul_le_mul' le_rfl ih
        _ = _ := by
          change C * (C ^ order.length * _) = C ^ (order.length + 1) * _
          rw [pow_succ]
          ac_rfl

/-- Exact full-grid ordered-composition bound for every real p > 1. The
empty list has coefficient one and is the identity operator. -/
theorem iteratedGridMaximal_power_integral (D : ∀ i, DyadicGrid (d i))
    (hd : ∀ i, 0 < d i) (F : ProductPoint d → ℝ≥0∞) (hF : Measurable F)
    (p : ℝ) (hp : 1 < p) :
    (∫⁻ x, (iteratedGridMaximal D F x) ^ p) ≤
      (ENNReal.ofReal ((p / (p - 1)) ^ m)) ^ p * ∫⁻ x, (F x) ^ p := by
  have hp' : 0 ≤ p / (p - 1) :=
    div_nonneg (zero_lt_one.trans hp).le (sub_pos.mpr hp).le
  have hC : ((ENNReal.ofReal (p / (p - 1))) ^ p) ^ m =
      (ENNReal.ofReal ((p / (p - 1)) ^ m)) ^ p := by
    calc
      _ = ((ENNReal.ofReal (p / (p - 1))) ^ p) ^ (m : ℝ) :=
        (ENNReal.rpow_natCast _ m).symm
      _ = (ENNReal.ofReal (p / (p - 1))) ^ (p * (m : ℝ)) :=
        (ENNReal.rpow_mul _ _ _).symm
      _ = (ENNReal.ofReal (p / (p - 1))) ^ ((m : ℝ) * p) := by rw [mul_comm p]
      _ = ((ENNReal.ofReal (p / (p - 1))) ^ m) ^ p :=
        ENNReal.rpow_natCast_mul _ m p
      _ = _ := by rw [ENNReal.ofReal_pow hp']
  simpa only [iteratedGridMaximal, List.length_finRange, hC] using
    foldr_coordinateGridMaximal_power_integral D hd F hF p hp (List.finRange m)

theorem iteratedGridMaximal_power_integral_ae (D : ∀ i, DyadicGrid (d i))
    (hd : ∀ i, 0 < d i) (F : ProductPoint d → ℝ≥0∞)
    (hF : AEMeasurable F volume) (p : ℝ) (hp : 1 < p) :
    (∫⁻ x, (iteratedGridMaximal D F x) ^ p) ≤
      (ENNReal.ofReal ((p / (p - 1)) ^ m)) ^ p * ∫⁻ x, (F x) ^ p := by
  calc
    _ = ∫⁻ x, (iteratedGridMaximal D (hF.mk F) x) ^ p :=
      lintegral_congr_ae ((iteratedGridMaximal_ae_congr D F (hF.mk F)
        hF.ae_eq_mk).fun_comp (fun t => t ^ p))
    _ ≤ _ := iteratedGridMaximal_power_integral D hd (hF.mk F) hF.measurable_mk p hp
    _ = _ := congrArg ((ENNReal.ofReal ((p / (p - 1)) ^ m)) ^ p * ·)
      (lintegral_congr_ae (hF.ae_eq_mk.symm.fun_comp (fun t => t ^ p)))

private theorem familyMaximal_le_iteratedGridMaximal_ae
    (D : ∀ i, DyadicGrid (d i)) (f : ProductPoint d → ℝ)
    (hf : AEStronglyMeasurable f volume)
    (hlocal : ∀ Q : ∀ i, Box (Fin (d i)), IntegrableOn f (productBox Q) volume) :
    ∀ᵐ x ∂volume, familyMaximal (gridRectangles D) f x ≤
      iteratedGridMaximal D (fun y => ENNReal.ofReal |f y|) x := by
  let F : ProductPoint d → ℝ≥0∞ := fun x => ENNReal.ofReal |f x|
  have hF : AEMeasurable F volume := by
    simpa only [F, Real.enorm_eq_ofReal_abs] using hf.enorm
  have hiter := iteratedGridMaximal_ae_congr D F (hF.mk F) hF.ae_eq_mk
  filter_upwards [hiter] with x hx
  change familyMaximal (gridRectangles D) f x ≤ iteratedGridMaximal D F x
  rw [hx]
  apply iSup_le
  intro Q
  by_cases hxQ : x ∈ productBox Q.1
  · rw [Set.indicator_of_mem hxQ]
    have hmean : ENNReal.ofReal ((∫ y in productBox Q.1, |f y|) /
        volume.real (productBox Q.1)) =
        (volume (productBox Q.1))⁻¹ * ∫⁻ y in productBox Q.1, F y := by
      have hi := ofReal_integral_eq_lintegral_ofReal (hlocal Q.1).abs
        (Filter.Eventually.of_forall (fun y => abs_nonneg (f y)))
      rw [ENNReal.ofReal_div_of_pos (productBox_volume_pos Q.1), measureReal_def,
        ENNReal.ofReal_toReal (productBox_volume_lt_top Q.1).ne, hi,
        div_eq_mul_inv, mul_comm]
    calc
      _ = (volume (productBox Q.1))⁻¹ * ∫⁻ y in productBox Q.1, F y := hmean
      _ = (volume (productBox Q.1))⁻¹ * ∫⁻ y in productBox Q.1, hF.mk F y :=
        congrArg ((volume (productBox Q.1))⁻¹ * ·)
          (lintegral_congr_ae (ae_restrict_of_ae hF.ae_eq_mk))
      _ ≤ _ := by
        simpa only [Set.indicator_of_mem hxQ] using
          productAverage_le_iteratedGridMaximal D (hF.mk F) hF.measurable_mk
            Q.1 Q.property x
  · rw [Set.indicator_of_notMem hxQ, ENNReal.ofReal_zero]
    exact zero_le

/-- The middle expression in the ordinary rectangular maximal
estimate, for arbitrary signed Lp input. Finiteness is established before
the real-valued representatives are used in the norm chain. -/
theorem ordinary_coordinate_composition (D : ∀ i, DyadicGrid (d i))
    (hd : ∀ i, 0 < d i) (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    let T := iteratedGridMaximal D (fun x => ENNReal.ofReal |f x|)
    AEMeasurable T volume ∧
    (∀ᵐ x ∂volume, T x < ∞) ∧
    MemLp (fun x => (T x).toReal) (ENNReal.ofReal p) volume ∧
    (∀ᵐ x ∂volume, familyMaximal (gridRectangles D) f x ≤ T x) ∧
    eLpNorm (fun x => (familyMaximal (gridRectangles D) f x).toReal)
        (ENNReal.ofReal p) volume ≤
      eLpNorm (fun x => (T x).toReal) (ENNReal.ofReal p) volume ∧
    eLpNorm (fun x => (T x).toReal) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((p / (p - 1)) ^ m) * eLpNorm f (ENNReal.ofReal p) volume := by
  let F : ProductPoint d → ℝ≥0∞ := fun x => ENNReal.ofReal |f x|
  let T := iteratedGridMaximal D F
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpE : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have hF : AEMeasurable F volume := by
    simpa only [F, Real.enorm_eq_ofReal_abs] using hf.aestronglyMeasurable.enorm
  have hTm : AEMeasurable T volume := aemeasurable_iteratedGridMaximal D F hF
  have hin : (∫⁻ x, (F x) ^ p) < ∞ := by
    simpa only [F, Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal hp0.le] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hpE ENNReal.ofReal_ne_top hf.eLpNorm_lt_top
  have hpower : (∫⁻ x, (T x) ^ p) ≤
      (ENNReal.ofReal ((p / (p - 1)) ^ m)) ^ p * ∫⁻ x, (F x) ^ p :=
    iteratedGridMaximal_power_integral_ae D hd F hF p hp
  have hout : (∫⁻ x, (T x) ^ p) < ∞ := lt_of_le_of_lt hpower
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hp0.le ENNReal.ofReal_ne_top) hin)
  have hfinite : ∀ᵐ x ∂volume, T x < ∞ := by
    filter_upwards [ae_lt_top' (hTm.pow_const p) hout.ne] with x hx
    exact (ENNReal.rpow_lt_top_iff_of_pos hp0).mp hx
  have hTlp : MemLp (fun x => (T x).toReal) (ENNReal.ofReal p) volume :=
    memLp_toReal_of_power_integral volume T hTm p hp0 hout
  have hlocal (Q : ∀ i, Box (Fin (d i))) : IntegrableOn f (productBox Q) volume := by
    let : IsFiniteMeasure (volume.restrict (productBox Q)) :=
      isFiniteMeasure_restrict.mpr (productBox_volume_lt_top Q).ne
    exact MemLp.integrable hp1 (hf.restrict (productBox Q))
  have hdom : ∀ᵐ x ∂volume, familyMaximal (gridRectangles D) f x ≤ T x :=
    familyMaximal_le_iteratedGridMaximal_ae D f hf.aestronglyMeasurable hlocal
  have hM : AEStronglyMeasurable
      (fun x => (familyMaximal (gridRectangles D) f x).toReal) volume :=
    ((measurable_familyMaximal (gridRectangles D)
      (countable_gridRectangles D) f).ennreal_toReal).aestronglyMeasurable
  have hnormMono :
      eLpNorm (fun x => (familyMaximal (gridRectangles D) f x).toReal)
          (ENNReal.ofReal p) volume ≤
        eLpNorm (fun x => (T x).toReal) (ENNReal.ofReal p) volume := by
    apply eLpNorm_mono_ae hM
    filter_upwards [hfinite, hdom] with x hx hle
    simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using
      ENNReal.toReal_mono hx.ne hle
  have hnorm : eLpNorm (fun x => (T x).toReal) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((p / (p - 1)) ^ m) * eLpNorm f (ENNReal.ofReal p) volume := by
    have heq : (∫⁻ x, ‖(T x).toReal‖ₑ ^ p) = ∫⁻ x, (T x) ^ p := by
      apply lintegral_congr_ae
      filter_upwards [hfinite] with x hx
      exact congrArg (fun t : ℝ≥0∞ => t ^ p) (Real.enorm_toReal hx.ne)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpE ENNReal.ofReal_ne_top
        hTlp.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hpE ENNReal.ofReal_ne_top
        hf.aestronglyMeasurable,
      ENNReal.toReal_ofReal hp0.le, heq]
    simp_rw [Real.enorm_eq_ofReal_abs]
    have h := ENNReal.rpow_le_rpow hpower (one_div_nonneg.mpr hp0.le)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp0.le),
      ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] at h
    exact h
  exact ⟨hTm, hfinite, hTlp, hdom, hnormMono, hnorm⟩

end ReyZygmund
