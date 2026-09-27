import ReyZygmund.Projection.SourceRepresentation
import ReyZygmund.Maximal.Reduction
import ReyZygmund.Maximal.GeneralInput
import ReyZygmund.Weighted.ProjectedHolderNorm
import ReyZygmund.Geometry.ProductLp

/-! # Finite reduction and the Hölder norm estimate

The common smallest side length and the input determine the finite step function.
Its constancy on the smallest cubes gives finiteness of all three norms. The
finite power-integral estimates then give the norm inequalities without additional
boundedness or scale-compatibility assumptions.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

private theorem finite_source_norm_data
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (G : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ)
    (hf : ProductLeafConstant I N f) (hs : ∀ x, x ∉ productBox I → f x = 0) :
    let u := finiteInput I N f hf
    let F := finiteProjectionMap I N G u
    let M := finiteFunctionMaximal (averagingRectangles I N G) f
    let W := finiteComplementSquareFunction I N F
    u.1 = f ∧ ProductLeafConstant I N M ∧ ProductLeafConstant I N W := by
  let u := finiteInput I N f hf
  have hu : u.1 = f := by
    funext x
    by_cases hx : x ∈ productBox I
    · exact Set.indicator_of_mem hx f
    · change (productBox I).indicator f x = f x
      rw [Set.indicator_of_notMem hx, hs x hx]
  have hul : ProductLeafConstant I N u.1 := by rw [hu]; exact hf
  have hus : ∀ x, x ∉ productBox I → u.1 x = 0 := by rw [hu]; exact hs
  have hF := finiteProjectionMap_productStep_closure I N G u hul hus
  refine ⟨hu, ?_, productLeafConstant_finiteComplementSquareFunction I N
    (finiteProjectionMap I N G u) hF.1 hF.2⟩
  rw [← hu, finiteFunctionMaximal_of_bounded]
  exact productLeafConstant_finiteFamilyMaximal I N (averagingRectangles I N G)
    (averagingRectangles_subset_productDescendants I N G) u

/-- The maximal-to-square estimate at a common smallest scale on arbitrary grids. The
dimension constant is uniform in the grids, top rectangle, scale, family, input
and exponent. -/
theorem source_maximal_to_square
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i)
    (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubes (n i))
    (G : Finset (∀ i, Box (Fin (d i)))) (hne : G.Nonempty)
    (hG : ∀ R ∈ G, R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
      ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u)
    (_hinc : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → R = S)
    (f : ProductPoint d → ℝ) (hs : ∀ x, x ∉ productBox I → f x = 0)
    (hfpos : ∀ x ∈ productBox I, 0 < f x)
    (hf : ∀ R, (R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
      ∀ i u, (R i).upper u - (R i).lower u = (2 : ℝ) ^ (-k)) →
      ∀ x ∈ productBox R, ∀ y ∈ productBox R, f x = f y)
    (p : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 : ℝ) / 2) :
    let N := fun i => (k - n i).toNat
    ∃ hleaf : ProductLeafConstant I N f,
      let u := finiteInput I N f hleaf
      let F := finiteProjectionMap I N G u
      let M := finiteFunctionMaximal (averagingRectangles I N G) f
      let W := finiteComplementSquareFunction I N F
      let μ := volume.restrict (productBox I)
      let C := (m : ℝ) * (2 : ℝ) ^ m *
        ((2 : ℝ) ^ (6 * (∑ i, d i) + 10) + (2 : ℝ) ^ (m - 1))
      u.1 = f ∧ MemLp f (ENNReal.ofReal p) μ ∧
      MemLp M (ENNReal.ofReal p) μ ∧ MemLp W (ENNReal.ofReal p) μ ∧
      eLpNorm M (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (C * (p / (p - 1)) ^ (m - 2)) * eLpNorm f (ENNReal.ofReal p) μ +
        ENNReal.ofReal C * eLpNorm W (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hnk : ∀ i, n i ≤ k :=
    (source_cutoff_or_empty hd D n k I hI G hG).resolve_right
      (Finset.nonempty_iff_ne_empty.mp hne)
  let N := fun i => (k - n i).toNat
  have hleaf : ProductLeafConstant I N f :=
    (source_productLeafConstant_iff hd D n k I hI hnk f).mpr hf
  let u := finiteInput I N f hleaf
  let F := finiteProjectionMap I N G u
  let M := finiteFunctionMaximal (averagingRectangles I N G) f
  let W := finiteComplementSquareFunction I N F
  let μ := volume.restrict (productBox I)
  let C := (m : ℝ) * (2 : ℝ) ^ m *
    ((2 : ℝ) ^ (6 * (∑ i, d i) + 10) + (2 : ℝ) ^ (m - 1))
  obtain ⟨hu, hMleaf, hWleaf⟩ := finite_source_norm_data I N G f hleaf hs
  have hfu : ProductLeafConstant I N u.1 := by rw [hu]; exact hleaf
  have hus : ∀ x, x ∉ productBox I → u.1 x = 0 := by rw [hu]; exact hs
  have hup : ∀ x ∈ productBox I, 0 ≤ u.1 x := by
    rw [hu]
    exact fun x hx => (hfpos x hx).le
  have hmax : M = finiteFamilyMaximal (averagingRectangles I N G) u := by
    rw [← finiteFunctionMaximal_of_bounded, hu]
  have hM0 (x) : 0 ≤ M x := by rw [hmax]; exact finiteFamilyMaximal_nonneg _ u x
  have hW0 (x) : 0 ≤ W x := Real.sqrt_nonneg _
  have hfm := memLp_productLeafConstant I N f hleaf p hp0
  have hMm := memLp_productLeafConstant I N M hMleaf p hp0
  have hWm := memLp_productLeafConstant I N W hWleaf p hp0
  refine ⟨hleaf, hu, hfm, hMm, hWm, ?_⟩
  change eLpNorm M (ENNReal.ofReal p) μ ≤
    ENNReal.ofReal (C * (p / (p - 1)) ^ (m - 2)) * eLpNorm f (ENNReal.ofReal p) μ +
    ENNReal.ofReal C * eLpNorm W (ENNReal.ofReal p) μ
  have hraw :
      Real.rpow (∫ x in productBox I, Real.rpow (M x) p) (1 / p) ≤
        C * (p / (p - 1)) ^ (m - 2) *
          Real.rpow (∫ x in productBox I, Real.rpow |f x| p) (1 / p) +
        C * Real.rpow (∫ x in productBox I, Real.rpow (W x) p) (1 / p) := by
    have h := finite_maximal_to_square hm I N hd G u hfu hus hup p hp hp3
    rw [← hmax] at h
    change Real.rpow (∫ x in productBox I, Real.rpow (M x) p) (1 / p) ≤
      C * (p / (p - 1)) ^ (m - 2) *
        Real.rpow (∫ x in productBox I, Real.rpow |u.1 x| p) (1 / p) +
      C * Real.rpow (∫ x in productBox I, Real.rpow (W x) p) (1 / p) at h
    rw [hu] at h
    exact h
  have hreal : lpNorm M (ENNReal.ofReal p) μ ≤
      (C * (p / (p - 1)) ^ (m - 2)) * lpNorm f (ENNReal.ofReal p) μ +
        C * lpNorm W (ENNReal.ofReal p) μ := by
    rw [lpNorm_productLeafConstant_eq I N M hMleaf p hp0,
      lpNorm_productLeafConstant_eq I N f hleaf p hp0,
      lpNorm_productLeafConstant_eq I N W hWleaf p hp0]
    simpa only [abs_of_nonneg (hM0 _), abs_of_nonneg (hW0 _)] using hraw
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCq : 0 ≤ C * (p / (p - 1)) ^ (m - 2) :=
    mul_nonneg hC (pow_nonneg (div_nonneg hp0.le (sub_pos.mpr hp).le) _)
  rw [← ofReal_lpNorm hMm, ← ofReal_lpNorm hfm, ← ofReal_lpNorm hWm]
  calc
    _ ≤ ENNReal.ofReal ((C * (p / (p - 1)) ^ (m - 2)) *
        lpNorm f (ENNReal.ofReal p) μ + C * lpNorm W (ENNReal.ofReal p) μ) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      rw [ENNReal.ofReal_add (mul_nonneg hCq lpNorm_nonneg)
        (mul_nonneg hC lpNorm_nonneg)]
      exact congrArg₂ (fun a b : ℝ≥0∞ => a + b)
        (ENNReal.ofReal_mul hCq) (ENNReal.ofReal_mul hC)

/-- The Hölder estimate for the averaging-family maximum and the common-projection
square function. Finiteness of the three norms is proved before converting the
power-integral estimate to norm form. -/
theorem source_holder_absorption
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i)
    (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubes (n i))
    (G : Finset (∀ i, Box (Fin (d i)))) (hne : G.Nonempty)
    (hG : ∀ R ∈ G, R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
      ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u)
    (_hinc : ∀ R ∈ G, ∀ S ∈ G, productBox R ⊆ productBox S → R = S)
    (f : ProductPoint d → ℝ) (hs : ∀ x, x ∉ productBox I → f x = 0)
    (hfpos : ∀ x ∈ productBox I, 0 < f x)
    (hf : ∀ R, (R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
      ∀ i u, (R i).upper u - (R i).lower u = (2 : ℝ) ^ (-k)) →
      ∀ x ∈ productBox R, ∀ y ∈ productBox R, f x = f y)
    (p : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 : ℝ) / 2) :
    let N := fun i => (k - n i).toNat
    ∃ hleaf : ProductLeafConstant I N f,
      let u := finiteInput I N f hleaf
      let F := finiteProjectionMap I N G u
      let M := finiteFunctionMaximal (averagingRectangles I N G) f
      let W := finiteComplementSquareFunction I N F
      let μ := volume.restrict (productBox I)
      let C := Real.sqrt ((m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)))
      u.1 = f ∧ MemLp f (ENNReal.ofReal p) μ ∧
      MemLp M (ENNReal.ofReal p) μ ∧ MemLp W (ENNReal.ofReal p) μ ∧
      eLpNorm W (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (C * Real.rpow (p - 1) (-((m - 1 : ℕ) : ℝ) / 2)) *
        (eLpNorm f (ENNReal.ofReal p) μ) ^ (p / 2) *
        (eLpNorm M (ENNReal.ofReal p) μ) ^ (1 - p / 2) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hp2 : p ≤ 2 := by linarith
  have hnk : ∀ i, n i ≤ k :=
    (source_cutoff_or_empty hd D n k I hI G hG).resolve_right
      (Finset.nonempty_iff_ne_empty.mp hne)
  let N := fun i => (k - n i).toNat
  have hleaf : ProductLeafConstant I N f :=
    (source_productLeafConstant_iff hd D n k I hI hnk f).mpr hf
  have hGN : G ⊆ productDescendants I N := by
    intro R hR
    exact (source_productDescendants_iff hd D n k I hI hnk R).mpr (hG R hR)
  let u := finiteInput I N f hleaf
  let F := finiteProjectionMap I N G u
  let M := finiteFunctionMaximal (averagingRectangles I N G) f
  let W := finiteComplementSquareFunction I N F
  let μ := volume.restrict (productBox I)
  let C := Real.sqrt ((m : ℝ) * (2 : ℝ) ^ ((∑ i, d i) + (m - 1)))
  let K := C * Real.rpow (p - 1) (-((m - 1 : ℕ) : ℝ) / 2)
  obtain ⟨hu, hMleaf, hWleaf⟩ := finite_source_norm_data I N G f hleaf hs
  have hmax : M = finiteFamilyMaximal (averagingRectangles I N G) u := by
    rw [← finiteFunctionMaximal_of_bounded, hu]
  have hM0 (x) : 0 ≤ M x := by rw [hmax]; exact finiteFamilyMaximal_nonneg _ u x
  have hW0 (x) : 0 ≤ W x := Real.sqrt_nonneg _
  have hf0 (x) : 0 ≤ f x := by
    by_cases hx : x ∈ productBox I
    · exact (hfpos x hx).le
    · rw [hs x hx]
  have hfm := memLp_productLeafConstant I N f hleaf p hp0
  have hMm := memLp_productLeafConstant I N M hMleaf p hp0
  have hWm := memLp_productLeafConstant I N W hWleaf p hp0
  refine ⟨hleaf, hu, hfm, hMm, hWm, ?_⟩
  change eLpNorm W (ENNReal.ofReal p) μ ≤
    ENNReal.ofReal K * (eLpNorm f (ENNReal.ofReal p) μ) ^ (p / 2) *
      (eLpNorm M (ENNReal.ofReal p) μ) ^ (1 - p / 2)
  have hraw :
      Real.rpow (∫ x in productBox I, Real.rpow (W x) p) (1 / p) ≤
        K * Real.rpow (Real.rpow (∫ x in productBox I, Real.rpow (f x) p) (1 / p))
          (p / 2) *
        Real.rpow (Real.rpow (∫ x in productBox I, Real.rpow (M x) p) (1 / p))
          (1 - p / 2) := by
    have h := projected_holder_norm_variables (by omega : 0 < m)
      I N hd G hGN f hleaf hfpos p hp hp2
    dsimp only at h
    rw [← hmax] at h
    exact h
  have hreal : lpNorm W (ENNReal.ofReal p) μ ≤
      K * Real.rpow (lpNorm f (ENNReal.ofReal p) μ) (p / 2) *
        Real.rpow (lpNorm M (ENNReal.ofReal p) μ) (1 - p / 2) := by
    rw [lpNorm_productLeafConstant_eq I N W hWleaf p hp0,
      lpNorm_productLeafConstant_eq I N f hleaf p hp0,
      lpNorm_productLeafConstant_eq I N M hMleaf p hp0]
    simpa only [abs_of_nonneg (hW0 _), abs_of_nonneg (hf0 _),
      abs_of_nonneg (hM0 _)] using hraw
  have hK : 0 ≤ K := mul_nonneg (Real.sqrt_nonneg _)
    (Real.rpow_nonneg (sub_pos.mpr hp).le _)
  have hhalf : 0 ≤ p / 2 := div_nonneg hp0.le (by norm_num)
  have hcomplement : 0 ≤ 1 - p / 2 := by linarith
  rw [← ofReal_lpNorm hWm, ← ofReal_lpNorm hfm, ← ofReal_lpNorm hMm]
  rw [ENNReal.ofReal_rpow_of_nonneg lpNorm_nonneg hhalf,
    ENNReal.ofReal_rpow_of_nonneg lpNorm_nonneg hcomplement]
  have hleft : 0 ≤ K * Real.rpow (lpNorm f (ENNReal.ofReal p) μ) (p / 2) :=
    mul_nonneg hK (Real.rpow_nonneg lpNorm_nonneg _)
  calc
    _ ≤ ENNReal.ofReal (K * Real.rpow (lpNorm f (ENNReal.ofReal p) μ) (p / 2) *
        Real.rpow (lpNorm M (ENNReal.ofReal p) μ) (1 - p / 2)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      rw [ENNReal.ofReal_mul hleft, ENNReal.ofReal_mul hK]
      rfl

end ReyZygmund
