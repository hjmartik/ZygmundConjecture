import ReyZygmund.Maximal.SignedFinite
import ReyZygmund.Geometry.GlobalDifferenceProperties
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Directed limits of signed rectangle maxima

Absolute values are outside the signed integrals. The finite-exhaustion identities
are algebraic; using their coefficients as averages requires integrability.
Uniform finite estimates give the limit inequalities for positive real powers,
including p = 1.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry

variable {m : ℕ} {d : Fin m → ℕ}

/-- A finite supremum of supported constant signed means is measurable,
including the zero supremum for the empty family. -/
theorem measurable_finiteSignedGridMaximal
    (H : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ) :
    Measurable (finiteSignedGridMaximal H f) := by
  induction H using Finset.induction_on with
  | empty =>
    have hzero : finiteSignedGridMaximal (∅ : Finset (∀ i, Box (Fin (d i)))) f =
        (fun _ : ProductPoint d => (0 : ℝ≥0∞)) := by
      funext x
      exact Finset.sup_empty
    rw [hzero]
    exact measurable_const
  | @insert Q H _ ih =>
    have hmean : Measurable (fun x : ProductPoint d =>
        ENNReal.ofReal ((productBox Q).indicator
          (fun _ => |(∫ y in productBox Q, f y) / volume.real (productBox Q)|) x)) :=
      (measurable_const.indicator (measurableSet_productBox Q)).ennreal_ofReal
    have hstep : finiteSignedGridMaximal (insert Q H) f =
        (fun x : ProductPoint d => ENNReal.ofReal ((productBox Q).indicator
          (fun _ => |(∫ y in productBox Q, f y) / volume.real (productBox Q)|) x) ⊔
            finiteSignedGridMaximal H f x) := by
      funext x
      exact Finset.sup_insert
    rw [hstep]
    exact hmean.sup ih

/-- Enlarging the finite family can only increase its signed maximum. -/
theorem finiteSignedGridMaximal_mono
    (H K : Finset (∀ i, Box (Fin (d i)))) (hHK : H ⊆ K)
    (f : ProductPoint d → ℝ) (x : ProductPoint d) :
    finiteSignedGridMaximal H f x ≤ finiteSignedGridMaximal K f x := by
  exact Finset.sup_mono hHK

private theorem finiteSignedGridMaximal_le_signedGridMaximal
    (D : ∀ i, DyadicGrid (d i)) (H : Finset (gridRectangles D))
    (f : ProductPoint d → ℝ) (x : ProductPoint d) :
    finiteSignedGridMaximal (H.image Subtype.val) f x ≤ signedGridMaximal D f x := by
  apply Finset.sup_le
  intro Q hQ
  obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hQ
  exact le_iSup (fun R : gridRectangles D => ENNReal.ofReal ((productBox R.1).indicator
    (fun _ => |(∫ y in productBox R.1, f y) / volume.real (productBox R.1)|) x)) R

/-- The full grid supremum is exactly the supremum of all its finite maxima.
The finite indices are grid rectangles, with no generation multiplicity. -/
theorem signedGridMaximal_eq_iSup_finset
    (D : ∀ i, DyadicGrid (d i)) (f : ProductPoint d → ℝ) (x : ProductPoint d) :
    signedGridMaximal D f x = ⨆ H : Finset (gridRectangles D),
      finiteSignedGridMaximal (H.image Subtype.val) f x := by
  apply le_antisymm
  · apply iSup_le
    intro Q
    apply le_iSup_of_le ({Q} : Finset (gridRectangles D))
    have hmem : Q.1 ∈ (({Q} : Finset (gridRectangles D)).image
        (Subtype.val : gridRectangles D → ∀ i, Box (Fin (d i)))) :=
      Finset.mem_image.mpr ⟨Q, Finset.mem_singleton_self Q, rfl⟩
    exact Finset.le_sup (f := fun R : ∀ i, Box (Fin (d i)) =>
      ENNReal.ofReal ((productBox R).indicator
        (fun _ => |(∫ y in productBox R, f y) / volume.real (productBox R)|) x)) hmem
  · exact iSup_le (fun H => finiteSignedGridMaximal_le_signedGridMaximal D H f x)

/-- Directed monotone convergence for positive real powers, allowing infinite
values and infinite integrals. Countability is derived from the grids. -/
theorem lintegral_signedGridMaximal_rpow_eq_iSup
    (D : ∀ i, DyadicGrid (d i)) (f : ProductPoint d → ℝ)
    (p : ℝ) (hp : 0 < p) :
    (∫⁻ x, (signedGridMaximal D f x) ^ p) =
      ⨆ H : Finset (gridRectangles D), ∫⁻ x,
        (finiteSignedGridMaximal (H.image Subtype.val) f x) ^ p := by
  have := (countable_gridRectangles D).to_subtype
  let F (H : Finset (gridRectangles D)) (x : ProductPoint d) : ℝ≥0∞ :=
    (finiteSignedGridMaximal (H.image Subtype.val) f x) ^ p
  have hmeas (H : Finset (gridRectangles D)) : Measurable (F H) :=
    (measurable_finiteSignedGridMaximal (H.image Subtype.val) f).pow_const p
  have hmono : Monotone F := by
    intro H K hHK x
    exact ENNReal.rpow_le_rpow
      (finiteSignedGridMaximal_mono _ _ (Finset.image_mono Subtype.val hHK) f x) hp.le
  have hdir : Directed (· ≤ ·) F := by
    intro H K
    exact ⟨H ∪ K, hmono Finset.subset_union_left, hmono Finset.subset_union_right⟩
  have heq (x : ProductPoint d) : (signedGridMaximal D f x) ^ p =
      ⨆ H : Finset (gridRectangles D), F H x := by
    rw [signedGridMaximal_eq_iSup_finset]
    exact (ENNReal.orderIsoRpow p hp).map_iSup
      (fun H : Finset (gridRectangles D) => finiteSignedGridMaximal (H.image Subtype.val) f x)
  calc
    _ = ∫⁻ x, ⨆ H : Finset (gridRectangles D), F H x := lintegral_congr heq
    _ = ⨆ H : Finset (gridRectangles D), ∫⁻ x, F H x :=
      lintegral_iSup_directed_of_measurable hmeas hdir

/-- A uniform bound for every finite subfamily passes to the full grid.
This statement supplies no estimate without its displayed finite hypotheses. -/
theorem lintegral_signedGridMaximal_rpow_le
    (D : ∀ i, DyadicGrid (d i)) (f : ProductPoint d → ℝ)
    (p : ℝ) (hp : 0 < p) (C : ℝ≥0∞)
    (hfinite : ∀ H : Finset (gridRectangles D),
      (∫⁻ x, (finiteSignedGridMaximal (H.image Subtype.val) f x) ^ p) ≤ C) :
    (∫⁻ x, (signedGridMaximal D f x) ^ p) ≤ C := by
  rw [lintegral_signedGridMaximal_rpow_eq_iSup D f p hp]
  exact iSup_le hfinite

/-- Finiteness of the extended power integral gives AE finiteness
before any real representative is taken. -/
theorem signedGridMaximal_ae_finite_of_lintegral_lt_top
    (D : ∀ i, DyadicGrid (d i)) (f : ProductPoint d → ℝ)
    (p : ℝ) (hp : 0 < p) (hfinite : (∫⁻ x, (signedGridMaximal D f x) ^ p) < ∞) :
    ∀ᵐ x ∂volume, signedGridMaximal D f x < ∞ := by
  have ha := ae_lt_top ((measurable_signedGridMaximal D f).pow_const p) hfinite.ne
  filter_upwards [ha] with x hx
  exact (ENNReal.rpow_lt_top_iff_of_pos hp).mp hx

/-- The real representative is in Lp once the full extended power integral
is finite. Its enorm is identified only on the proved AE finite set. -/
theorem memLp_signedGridMaximal_toReal_of_lintegral_lt_top
    (D : ∀ i, DyadicGrid (d i)) (f : ProductPoint d → ℝ)
    (p : ℝ) (hp : 0 < p) (hfinite : (∫⁻ x, (signedGridMaximal D f x) ^ p) < ∞) :
    MemLp (fun x => (signedGridMaximal D f x).toReal) (ENNReal.ofReal p) volume := by
  have hm : AEStronglyMeasurable (fun x => (signedGridMaximal D f x).toReal) volume :=
    (measurable_signedGridMaximal D f).ennreal_toReal.aestronglyMeasurable
  have hae := signedGridMaximal_ae_finite_of_lintegral_lt_top D f p hp hfinite
  apply memLp_iff.mpr
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top hm).mpr
  rw [ENNReal.toReal_ofReal hp.le]
  calc
    (∫⁻ x, ‖(signedGridMaximal D f x).toReal‖ₑ ^ p) =
        ∫⁻ x, (signedGridMaximal D f x) ^ p := by
      apply lintegral_congr_ae
      filter_upwards [hae] with x hx
      rw [Real.enorm_toReal hx.ne]
    _ < ∞ := hfinite

end ReyZygmund
