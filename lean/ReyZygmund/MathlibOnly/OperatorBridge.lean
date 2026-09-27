import ReyZygmund.MathlibOnly.Statements
import Verification.Challenges.Endpoints
import Verification.Challenges.PhiSparse
import ReyZygmund.Geometry.ProductJensen
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Equality of the independently defined operators

These lemmas identify the rectangle sets, extended averages, sparse subsets and
prescribed scale families with those in the proof library. This file imports the
proofs; the independent definition and statement files import only Mathlib.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.MathlibOnly

noncomputable section

theorem rectangle_eq_challenge {m : ℕ} {d : Fin m → ℕ}
    (R : ∀ i, Box (Fin (d i))) :
    rectangle R = ReyZygmundVerification.Challenges.rectangle R := rfl

theorem rectangle_eq_flat {m : ℕ} {d : Fin m → ℕ}
    (R : ∀ i, Box (Fin (d i))) :
    rectangle R = (Geometry.flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) := by
  ext x
  obtain ⟨y, rfl⟩ := (Geometry.flattenCoordinates d).surjective x
  apply Iff.trans _ (Geometry.mem_flatProductBox R y).symm
  simp only [rectangle, Set.mem_ofPred_eq, Geometry.mem_productBox,
    Geometry.flattenCoordinates_apply]
  rfl

theorem shadow_eq_challenge {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i)))) :
    shadow G = ReyZygmundVerification.Challenges.shadow G := rfl

theorem overlap_eq_challenge {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i)))) :
    overlap G = ReyZygmundVerification.Challenges.overlap G := rfl

theorem sparse_iff_challenge {m : ℕ} {d : Fin m → ℕ} (eta : ℝ)
    (G : Set (∀ i, Box (Fin (d i)))) :
    Sparse eta G ↔ ReyZygmundVerification.Challenges.sparse eta G := by
  constructor
  · rintro ⟨E, hE, hdis⟩
    exact ⟨E, (fun R hR => (hE R hR).1), (fun R hR => (hE R hR).2.1),
      hdis, (fun R hR => (hE R hR).2.2)⟩
  · rintro ⟨E, hm, hsub, hdis, hvol⟩
    exact ⟨E, (fun R hR => ⟨hm R hR, hsub R hR, hvol R hR⟩), hdis⟩

theorem maximal_eq_challenge {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i)))) (f : (Fin (∑ i, d i) → ℝ) → ℝ) :
    maximal G f = ReyZygmundVerification.Challenges.absoluteMaximal G f := rfl

/-- Locally integrable input justifies every real average before identifying
the extended supremum; this also covers infinite Orlicz integrals. -/
theorem maximal_eq_endpoint {m : ℕ} {d : Fin m → ℕ}
    (G : Set (∀ i, Box (Fin (d i)))) (f : (Fin (∑ i, d i) → ℝ) → ℝ)
    (hf : LocallyIntegrable f volume) :
    maximal G f = ReyZygmundVerification.Challenges.endpointMaximal G f := by
  funext x
  unfold maximal ReyZygmundVerification.Challenges.endpointMaximal
  congr 1
  funext R
  rw [rectangle_eq_flat]
  have hv : volume (Geometry.flatProductBox R.1 : Set (Fin (∑ i, d i) → ℝ)) < ∞ := by
    rw [Geometry.volume_flatProductBox]
    exact Geometry.productBox_volume_lt_top R.1
  have hvpos : 0 < volume.real
      (Geometry.flatProductBox R.1 : Set (Fin (∑ i, d i) → ℝ)) := by
    rw [Measure.real, Geometry.volume_flatProductBox]
    exact Geometry.productBox_volume_pos R.1
  have hlocal : IntegrableOn f
      (Geometry.flatProductBox R.1 : Set (Fin (∑ i, d i) → ℝ)) volume :=
    (hf.integrableOn_isCompact (Geometry.flatProductBox R.1).isCompact_Icc).mono_set
      Box.coe_subset_Icc
  by_cases hx : x ∈ (Geometry.flatProductBox R.1 : Set (Fin (∑ i, d i) → ℝ))
  · simp only [Set.indicator_of_mem hx]
    rw [ENNReal.ofReal_div_of_pos hvpos,
      ofReal_integral_eq_lintegral_ofReal hlocal.abs
        (Filter.Eventually.of_forall (fun y => abs_nonneg (f y))),
      Measure.real, ENNReal.ofReal_toReal hv.ne]
  · simp only [Set.indicator_of_notMem hx, ENNReal.ofReal_zero]

theorem continuousRectangles_eq {n : ℕ} (d : Fin (n + 1) → ℕ)
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) :
    continuousRectangles d phi = Geometry.continuousPhiRectangles d phi := rfl

theorem rounding_eq (s : ℝ) : rounding s = Geometry.roundedScale s := rfl

theorem roundedScales_eq {n : ℕ}
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) :
    roundedScales phi = Geometry.roundedScales phi := rfl

/-- The explicit side-exponent formula is exactly the implementation's
alternating grid at the negative generation. -/
theorem shiftedCubes_eq {d : ℕ} (tau : Fin d → Fin 3) (k : ℤ) :
    shiftedCubes tau k = (Geometry.shiftedDyadicGrid d tau).cubes (-k) := by
  ext Q
  change (∃ z : Fin d → ℤ, ∀ j, _ ∧ _) ↔
    ∃ z : Fin d → ℤ, Geometry.shiftedDyadicCube tau (-k) z = Q
  have hphase : (-1 : ℝ) ^ (-k) = (-1 : ℝ) ^ k := by
    simp only [neg_one_zpow_eq_ite, even_neg]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply Box.ext
    intro x
    simp only [Box.mem_def]
    apply forall_congr'
    intro j
    change (_ < x j ∧ x j ≤ _) ↔ _
    simp only [Geometry.shiftedDyadicCube, Geometry.rootBox, neg_neg, hphase]
    rw [← (hz j).1, ← (hz j).2]
    rfl
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    intro j
    simp [Geometry.shiftedDyadicCube, Geometry.rootBox, neg_neg, hphase]

theorem roundedRectangles_eq {n : ℕ} {d : Fin (n + 1) → ℕ}
    (tau : ∀ i, Fin (d i) → Fin 3)
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) :
    roundedRectangles tau phi = Geometry.roundedGridRectangles
      (fun i => Geometry.shiftedDyadicGrid (d i) (tau i)) phi := by
  simp only [roundedRectangles, Geometry.roundedGridRectangles,
    roundedScales_eq, shiftedCubes_eq]

end
end ReyZygmund.MathlibOnly
