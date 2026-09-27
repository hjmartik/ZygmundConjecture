import ReyZygmund.Geometry.FlatRectangles
import ReyZygmund.Geometry.RoundedSlices
import Mathlib.MeasureTheory.Measure.Prod

/-! # Splitting off the last coordinate

Flatten the first coordinates as in the overlap theorem. The resulting measurable
equivalence preserves Lebesgue measure and the half-open boxes.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal

namespace ReyZygmund.Geometry

variable {n : ℕ} (d : Fin (n + 1) → ℕ)

private def lastProductCoordinates : ProductPoint d ≃ᵐ
    ((Fin (d (Fin.last n)) → ℝ) × ProductPoint (fun i : Fin n => d i.castSucc)) where
  toFun x := (x (Fin.last n), fun i => x i.castSucc)
  invFun z := Fin.lastCases z.1 z.2
  left_inv x := by
    funext i
    exact Fin.lastCases (by simp) (fun j => by simp) i
  right_inv z := by simp
  measurable_toFun := (measurable_pi_apply _).prodMk
    (measurable_pi_iff.mpr (fun i => measurable_pi_apply i.castSucc))
  measurable_invFun := measurable_pi_iff.mpr (fun i =>
    Fin.lastCases (by simpa using (measurable_fst : Measurable fun z :
      (Fin (d (Fin.last n)) → ℝ) × ProductPoint (fun j : Fin n => d j.castSucc) => z.1))
      (fun j => by
        change Measurable (fun z :
          (Fin (d (Fin.last n)) → ℝ) × ProductPoint (fun k : Fin n => d k.castSucc) =>
            Fin.lastCases (motive := fun i => Fin (d i) → ℝ) z.1 z.2 j.castSucc)
        simpa only [Fin.lastCases_castSucc, Function.comp_def] using
          (measurable_pi_apply j).comp
            (measurable_snd : Measurable fun z :
              (Fin (d (Fin.last n)) → ℝ) × ProductPoint (fun k : Fin n => d k.castSucc) => z.2)) i)

private theorem lastProductCoordinates_apply (x : ProductPoint d) :
    lastProductCoordinates d x = (x (Fin.last n), fun i : Fin n => x i.castSucc) := rfl

private theorem volume_preserving_lastProductCoordinates :
    MeasurePreserving (lastProductCoordinates d) volume volume := by
  let e := (lastProductCoordinates d).symm
  apply MeasurePreserving.symm e
  refine ⟨e.measurable, ?_⟩
  change volume.map e = Measure.pi (fun i => (volume : Measure (Fin (d i) → ℝ)))
  refine (Measure.pi_eq (fun s _ => ?_)).symm
  rw [MeasurableEquiv.map_apply]
  have hset : e ⁻¹' Set.pi Set.univ s =
      s (Fin.last n) ×ˢ Set.pi Set.univ (fun i : Fin n => s i.castSucc) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    change (∀ i, Fin.lastCases z.1 z.2 i ∈ s i) ↔
      z.1 ∈ s (Fin.last n) ∧ ∀ i : Fin n, z.2 i ∈ s i.castSucc
    constructor
    · intro h
      exact ⟨by simpa using h (Fin.last n), fun i => by simpa using h i.castSucc⟩
    · rintro ⟨hlast, hfirst⟩ i
      exact Fin.lastCases (by simpa using hlast) (fun j => by simpa using hfirst j) i
  rw [hset]
  change ((volume : Measure (Fin (d (Fin.last n)) → ℝ)).prod
    (volume : Measure (ProductPoint (fun i : Fin n => d i.castSucc)))) _ = _
  rw [Measure.prod_prod, volume_pi_pi, Fin.prod_univ_castSucc, mul_comm]

/-- Split the last block from the usual flattened Euclidean coordinates. -/
noncomputable def splitLastCoordinates : (Fin (∑ i, d i) → ℝ) ≃ᵐ
    ((Fin (∑ i : Fin n, d i.castSucc) → ℝ) × (Fin (d (Fin.last n)) → ℝ)) :=
  (flattenCoordinates d).symm.trans ((lastProductCoordinates d).trans
    (MeasurableEquiv.prodComm.trans
      ((flattenCoordinates (fun i : Fin n => d i.castSucc)).prodCongr
        (MeasurableEquiv.refl _))))

theorem splitLastCoordinates_apply (x : ProductPoint d) :
    splitLastCoordinates d (flattenCoordinates d x) =
      (flattenCoordinates (fun i : Fin n => d i.castSucc) (fun i => x i.castSucc),
        x (Fin.last n)) := by
  simp only [splitLastCoordinates, MeasurableEquiv.trans_apply,
    MeasurableEquiv.symm_apply_apply, lastProductCoordinates_apply]
  rfl

theorem volume_preserving_splitLastCoordinates :
    MeasurePreserving (splitLastCoordinates d) volume volume := by
  exact (volume_preserving_flattenCoordinates d).symm
    (flattenCoordinates d) |>.trans
      ((volume_preserving_lastProductCoordinates d).trans
        (Measure.measurePreserving_swap.trans
          ((volume_preserving_flattenCoordinates (fun i : Fin n => d i.castSucc)).prod
            (MeasurePreserving.id volume))))

theorem splitLastCoordinates_mem_rectangle
    (R : ∀ i, Box (Fin (d i))) (x : Fin (∑ i, d i) → ℝ) :
    x ∈ flatProductBox R ↔
      splitLastCoordinates d x ∈
        ((flatProductBox (initialProjection R) :
          Set (Fin (∑ i : Fin n, d i.castSucc) → ℝ)) ×ˢ
          (R (Fin.last n) : Set (Fin (d (Fin.last n)) → ℝ))) := by
  obtain ⟨y, rfl⟩ := (flattenCoordinates d).surjective x
  rw [splitLastCoordinates_apply, mem_flatProductBox, Set.mem_prod]
  change y ∈ productBox R ↔
    flattenCoordinates (fun i : Fin n => d i.castSucc) (fun i => y i.castSucc) ∈
      flatProductBox (initialProjection R) ∧ y (Fin.last n) ∈ R (Fin.last n)
  rw [mem_flatProductBox, mem_productBox, mem_productBox]
  constructor
  · intro h
    exact ⟨fun i => h i.castSucc, h (Fin.last n)⟩
  · rintro ⟨hfirst, hlast⟩ i
    exact Fin.lastCases hlast hfirst i

/-- Nonnegative Fubini in the last-coordinate decomposition. -/
theorem lintegral_splitLastCoordinates
    (f : (Fin (∑ i, d i) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x) = ∫⁻ t, ∫⁻ y, f ((splitLastCoordinates d).symm (y, t)) := by
  let e := splitLastCoordinates d
  have h := (volume_preserving_splitLastCoordinates d).symm e
  rw [← h.lintegral_comp (hf)]
  exact lintegral_prod_symm _ (hf.comp e.symm.measurable).aemeasurable

end ReyZygmund.Geometry
