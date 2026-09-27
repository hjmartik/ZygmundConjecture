import ReyZygmund.Selection.Shadow
import ReyZygmund.Selection.SliceSparsity
import ReyZygmund.Geometry.FiniteSlices
import ReyZygmund.Overlap.FiniteExponential

/-! # Exponential integrability of the selected rounded family

The half-overlap bound makes the full family incomparable. Each last-coordinate
slice is half-sparse and satisfies weaker containment. The overlap estimate and
nonnegative Fubini give power `1 / (m - 2)`. We integrate the original finite
overlap, so no jointly measurable choice of the disjoint subsets in the slices is
needed.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Selection

open Geometry Overlap

/-- Constants are fixed before the grids, side function and selected family.
This intermediate is indexed by the dimension vector; the main endpoint
statement separately makes the dependence on total dimension uniform. -/
theorem selected_rounded_exponential
    (n : ℕ) (d : Fin (n + 1) → ℕ) (hn : 2 ≤ n) (hd : ∀ i, 0 < d i) :
    ∃ c B : ℝ, 0 < c ∧ 0 < B ∧
      ∀ (D : ∀ i, DyadicGrid (d i))
        (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)), Monotone phi →
      ∀ G : Finset (∀ i, Box (Fin (d i))),
      (↑G : Set (∀ i, Box (Fin (d i)))) ⊆ roundedGridRectangles D phi →
      (∀ R ∈ G,
        volume.real ((flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ∩
          finiteShadow (G.erase R)) ≤
          (1 / 2 : ℝ) * volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) →
      (∫⁻ x in finiteShadow G, ENNReal.ofReal
        (Real.exp (c * Real.rpow (finiteOverlap G x) (1 / ((n - 1 : ℕ) : ℝ))))) ≤
        ENNReal.ofReal B * volume (finiteShadow G) := by
  obtain ⟨c, B, hc, hB, hspec⟩ := finite_half_sparse_exponential
  let Dfirst := ∑ i : Fin n, d i.castSucc
  refine ⟨c n Dfirst, B n Dfirst, hc _ _, hB _ _, ?_⟩
  intro D phi hphi G hG hoverlap
  have hgrid : (↑G : Set (∀ i, Box (Fin (d i)))) ⊆ gridRectangles D :=
    hG.trans (roundedGridRectangles_subset D phi)
  have hinc := incomparable_of_half_overlap G hoverlap
  have hslice (t : Fin (d (Fin.last n)) → ℝ) :
      (∫⁻ y in finiteShadow (finiteSlice G t), ENNReal.ofReal
        (Real.exp (c n Dfirst * Real.rpow (finiteOverlap (finiteSlice G t) y)
          (1 / ((n - 1 : ℕ) : ℝ))))) ≤
        ENNReal.ofReal (B n Dfirst) * volume (finiteShadow (finiteSlice G t)) := by
    obtain ⟨E, hE, hdis⟩ := finite_slice_half_sparse D G hgrid hoverlap t
    have heq := coe_finiteSlice G t
    have hsliceGrid : (↑(finiteSlice G t) : Set _) ⊆
        gridRectangles (fun i : Fin n => D i.castSucc) := by
      rw [heq]
      exact sliceFamily_subset_grid D (↑G) hgrid t
    have hweak : ∀ R ∈ finiteSlice G t, ∀ S ∈ finiteSlice G t,
        productBox R ⊆ productBox S → ∃ i, R i = S i := by
      intro R hR S hS hRS
      have hR' : R ∈ sliceFamily (↑G) t := by rw [← heq]; exact hR
      have hS' : S ∈ sliceFamily (↑G) t := by rw [← heq]; exact hS
      exact sliceFamily_weaker_containment (by omega) D phi hphi (↑G) hG hinc t
        R hR' S hS' ((productBox_subset_iff R S).mp hRS)
    rw [← heq] at hE hdis
    exact hspec n (fun i => d i.castSucc) hn (fun i => hd i.castSucc)
      (fun i => D i.castSucc) (finiteSlice G t) hsliceGrid hweak E
      (fun R hR => (hE R hR).1) (fun R hR => (hE R hR).2.1) hdis
      (fun R hR => (hE R hR).2.2)
  let f := fun x => ENNReal.ofReal
    (Real.exp (c n Dfirst * Real.rpow (finiteOverlap G x) (1 / ((n - 1 : ℕ) : ℝ))))
  have hf : Measurable f := by
    dsimp [f]
    simpa only [Real.rpow_eq_pow] using
      (((measurable_finiteOverlap G).pow_const (1 / ((n - 1 : ℕ) : ℝ))).const_mul
        (c n Dfirst)).exp.ennreal_ofReal
  have hsplit :
      (∫⁻ x in finiteShadow G, f x) =
        ∫⁻ t, ∫⁻ y in finiteShadow (finiteSlice G t), ENNReal.ofReal
          (Real.exp (c n Dfirst * Real.rpow (finiteOverlap (finiteSlice G t) y)
            (1 / ((n - 1 : ℕ) : ℝ)))) := by
    rw [← lintegral_indicator (measurableSet_finiteShadow G)]
    rw [lintegral_splitLastCoordinates d _ (hf.indicator (measurableSet_finiteShadow G))]
    apply lintegral_congr
    intro t
    rw [← lintegral_indicator (measurableSet_finiteShadow (finiteSlice G t))]
    apply lintegral_congr
    intro y
    simp only [Set.indicator, mem_finiteShadow_splitLast_symm, f,
      finiteOverlap_splitLast_symm D G hgrid hinc]
  change (∫⁻ x in finiteShadow G, f x) ≤ _
  rw [hsplit]
  calc
    _ ≤ ∫⁻ t, ENNReal.ofReal (B n Dfirst) *
        volume (finiteShadow (finiteSlice G t)) := lintegral_mono hslice
    _ = ENNReal.ofReal (B n Dfirst) * volume (finiteShadow G) := by
      rw [lintegral_const_mul', ← volume_finiteShadow_slices G]
      exact ENNReal.ofReal_ne_top

end ReyZygmund.Selection
