import ReyZygmund.Selection.Variational
import ReyZygmund.Maximal.OrdinaryGrid

/-!
# The shadow bound for finite variational selection

Insertion gives a weak half-density inequality. The finite ordinary
maximal function is therefore at least one half on the original shadow.
Its squared L2 bound gives exactly `4 ^ (m + 1)`; no strict halo threshold
or incomparable maximal estimate is used.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Selection

open Geometry Overlap

variable {m : ℕ} {d : Fin m → ℕ}

/-- The analytic shadow comparison uses only the insertion densities and
the ordinary finite-grid L2 estimate. -/
theorem finite_density_shadow_bound
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (F G : Finset (∀ i, Box (Fin (d i)))) (hF : ↑F ⊆ gridRectangles D)
    (hdensity : ∀ Q ∈ F,
      (1 / 2 : ℝ) * volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ≤
        volume.real ((flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∩ finiteShadow G)) :
    volume.real (finiteShadow F) ≤ (4 : ℝ) ^ (m + 1) * volume.real (finiteShadow G) := by
  let S := flattenCoordinates d ⁻¹' finiteShadow F
  let A := flattenCoordinates d ⁻¹' finiteShadow G
  let f : ProductPoint d → ℝ := A.indicator (fun _ => 1)
  have hSmeas : MeasurableSet S :=
    (measurableSet_finiteShadow F).preimage (flattenCoordinates d).measurable
  have hAmeas : MeasurableSet A :=
    (measurableSet_finiteShadow G).preimage (flattenCoordinates d).measurable
  have hSvol : volume S = volume (finiteShadow F) :=
    (volume_preserving_flattenCoordinates d).measure_preimage_equiv _
  have hAvol : volume A = volume (finiteShadow G) :=
    (volume_preserving_flattenCoordinates d).measure_preimage_equiv _
  have hSfin : volume S ≠ ∞ := hSvol.trans_ne (volume_finiteShadow_lt_top F).ne
  have hAfin : volume A ≠ ∞ := hAvol.trans_ne (volume_finiteShadow_lt_top G).ne
  have hf : MemLp f 2 volume := memLp_indicator_const 2 hAmeas 1 (Or.inr hAfin)
  have havg (Q : ∀ i, Box (Fin (d i))) :
      (∫ y in productBox Q, |f y|) =
        volume.real ((flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∩ finiteShadow G) := by
    have heq : (fun y => |f y|) =
        (fun y => (finiteShadow G).indicator (fun _ => (1 : ℝ))
          (flattenCoordinates d y)) := by
      funext y
      by_cases hy : flattenCoordinates d y ∈ finiteShadow G
      · simp [f, A, hy]
      · simp [f, A, hy]
    rw [heq, integral_flatProductBox, setIntegral_indicator (measurableSet_finiteShadow G),
      setIntegral_const]
    simp
  have hpoint (x : ProductPoint d) :
      S.indicator (fun _ => (1 : ℝ)) x ≤ 4 * (finiteFunctionMaximal F f x) ^ 2 := by
    by_cases hx : x ∈ S
    · obtain ⟨Q, hQ, hxQ⟩ := Set.mem_iUnion₂.mp hx
      have hxQ' : x ∈ productBox Q := (mem_flatProductBox Q x).mp hxQ
      have havgHalf : (1 / 2 : ℝ) ≤
          (∫ y in productBox Q, |f y|) / volume.real (productBox Q) := by
        apply (le_div_iff₀ (productBox_volume_pos Q)).mpr
        rw [havg]
        simpa only [Measure.real, volume_flatProductBox] using hdensity Q hQ
      have hmax := positiveMean_le_finiteFunctionMaximal F f Q hQ x
      rw [Set.indicator_of_mem hxQ'] at hmax
      rw [Set.indicator_of_mem hx]
      nlinarith
    · rw [Set.indicator_of_notMem hx]
      positivity
  have hM : Integrable (fun x => (finiteFunctionMaximal F f x) ^ 2) volume := by
    simpa only [Real.rpow_eq_pow, Real.rpow_two] using
      integrable_rpow_finiteFunctionMaximal F f 2 (by norm_num)
  have hinput : (∫ x, |f x| ^ 2) = volume.real A := by
    have heq : (fun x => |f x| ^ 2) = A.indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ A <;> simp [f, hx]
    rw [heq, integral_indicator_const 1 hAmeas]
    simp
  have hL2 := finite_ordinary_grid_maximal_l2 hd D F hF f hf
  rw [hinput] at hL2
  have hbound : volume.real S ≤ 4 * ∫ x, (finiteFunctionMaximal F f x) ^ 2 := by
    rw [← integral_indicator_one hSmeas, ← integral_const_mul]
    exact integral_mono ((integrableOn_const hSfin).integrable_indicator hSmeas)
      (hM.const_mul 4) hpoint
  have hrealS : volume.real S = volume.real (finiteShadow F) := congrArg ENNReal.toReal hSvol
  have hrealA : volume.real A = volume.real (finiteShadow G) := congrArg ENNReal.toReal hAvol
  rw [hrealS] at hbound
  rw [hrealA] at hL2
  calc
    _ ≤ 4 * ∫ x, (finiteFunctionMaximal F f x) ^ 2 := hbound
    _ ≤ 4 * ((4 : ℝ) ^ m * volume.real (finiteShadow G)) := by linarith
    _ = _ := by rw [pow_succ]; ring

/-- The selected half-overlap property excludes every distinct containment. -/
theorem incomparable_of_half_overlap
    (G : Finset (∀ i, Box (Fin (d i))))
    (hoverlap : ∀ Q ∈ G,
      volume.real ((flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∩ finiteShadow (G.erase Q)) ≤
        (1 / 2 : ℝ) * volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ))) :
    ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S := by
  intro R hR S hS hRS
  by_contra hne
  have hsub : (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ⊆ (flatProductBox S : Set (Fin (∑ i, d i) → ℝ)) := by
    intro x hx
    obtain ⟨y, rfl⟩ := (flattenCoordinates d).surjective x
    apply (mem_flatProductBox S y).mpr
    apply (mem_productBox S y).mpr
    intro i
    exact hRS i ((mem_productBox R y).mp ((mem_flatProductBox R y).mp hx) i)
  have hshadow : (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ⊆ finiteShadow (G.erase R) :=
    hsub.trans (flatProductBox_subset_finiteShadow (G.erase R) S
      (Finset.mem_erase.mpr ⟨Ne.symm hne, hS⟩))
  have h := hoverlap R hR
  rw [Set.inter_eq_left.mpr hshadow] at h
  have hv : 0 < volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) := by
    simpa only [Measure.real, volume_flatProductBox] using productBox_volume_pos R
  linarith

/-- The paper's finite selection lemma with the stated explicit number of
coordinate factors in its shadow constant. -/
theorem finite_selection_with_comparable_shadow
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i))
    (F : Finset (∀ i, Box (Fin (d i)))) (hF : ↑F ⊆ gridRectangles D) :
    ∃ G : Finset (∀ i, Box (Fin (d i))), G ⊆ F ∧
      volume.real (finiteShadow F) ≤ (4 : ℝ) ^ (m + 1) * volume.real (finiteShadow G) ∧
      (∀ Q ∈ G,
        volume.real ((flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∩ finiteShadow (G.erase Q)) ≤
          (1 / 2 : ℝ) * volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ))) := by
  obtain ⟨G, hGF, _hmax, hoverlap, hdensity⟩ := finite_variational_selection F
  exact ⟨G, hGF, finite_density_shadow_bound hd D F G hF hdensity, hoverlap⟩

end ReyZygmund.Selection
