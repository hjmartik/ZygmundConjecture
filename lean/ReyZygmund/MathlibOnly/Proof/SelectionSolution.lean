import ReyZygmund.MathlibOnly.SupportingStatements
import ReyZygmund.Selection.Shadow

/-! # Córdoba–Fefferman selection

The variational selection supplies the half-overlap condition. Its insertion
inequality and the ordinary product maximal bound give the shadow comparison.
The finite-set conclusion below uses the same selected family.
-/

open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.MathlibOnly

open Geometry Overlap

/-- Selection with comparable shadow, uniformly in the factor dimensions and grids. -/
theorem cordoba_fefferman_selection : CordobaFeffermanSelection := by
  intro m _hm
  refine ⟨(4 : ℝ) ^ (m + 1), by positivity, ?_⟩
  intro d hd D F hfin hgrid
  obtain ⟨G, hGF, hshadow, hoverlap⟩ := Selection.finite_selection_with_comparable_shadow
    hd D hfin.toFinset (by simpa only [hfin.coe_toFinset] using hgrid)
  refine ⟨(G : Set (Rectangle d)), ?_, ?_, ?_⟩
  · intro R hR
    exact hfin.mem_toFinset.mp (hGF hR)
  · have hFfinite := (volume_finiteShadow_lt_top hfin.toFinset).ne
    have hGfinite := (volume_finiteShadow_lt_top G).ne
    have h := ENNReal.ofReal_le_ofReal hshadow
    rw [ENNReal.ofReal_mul (by positivity), ofReal_measureReal hFfinite,
      ofReal_measureReal hGfinite] at h
    simpa only [finiteShadow_eq_shadow, hfin.coe_toFinset] using h
  · intro R hR
    have hfinite : volume ((flatProductBox R : Set (Point d)) ∩
        finiteShadow (G.erase R)) ≠ ∞ :=
      measure_ne_top_of_subset Set.inter_subset_left
        (flatProductBox R).isBounded.measure_lt_top.ne
    have h := ENNReal.ofReal_le_ofReal (hoverlap R hR)
    rw [ENNReal.ofReal_mul (by norm_num), ofReal_measureReal hfinite,
      ofReal_measureReal (flatProductBox R).isBounded.measure_lt_top.ne] at h
    simpa only [finiteShadow_eq_shadow, Finset.coe_erase, rectangle_eq_flatProductBox,
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using h

end ReyZygmund.MathlibOnly
