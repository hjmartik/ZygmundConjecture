import ReyZygmund.Maximal.GeneralInput

/-! # Localization to disjoint top rectangles

For each top rectangle, take the subfamily it contains. Powers of the finite
maximal function are integrable, since a finite sum of constants supported on
finite-volume rectangles bounds them.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- Every supported absolute mean in the family is below its finite maximum. -/
theorem positiveMean_le_finiteFunctionMaximal
    (G : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ)
    (Q : ∀ i, Box (Fin (d i))) (hQ : Q ∈ G) (x : ProductPoint d) :
    (productRectangle Q).indicator
      (fun _ => (∫ y in productRectangle Q, |f y|) / volume.real (productRectangle Q)) x ≤
      finiteFunctionMaximal G f x := by
  rw [finiteFunctionMaximal, dite_eq_left ⟨Q, hQ⟩]
  exact Finset.le_sup' (fun R => (productRectangle R).indicator
    (fun _ => (∫ y in productRectangle R, |f y|) / volume.real (productRectangle R)) x) hQ

/-- The finite maximum is nonnegative. -/
theorem finiteFunctionMaximal_nonneg
    (G : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ)
    (x : ProductPoint d) : 0 ≤ finiteFunctionMaximal G f x := by
  by_cases h : G.Nonempty
  · obtain ⟨Q, hQ⟩ := h
    apply le_trans _ (positiveMean_le_finiteFunctionMaximal G f Q hQ x)
    exact Set.indicator_nonneg (fun _ _ =>
      div_nonneg (integral_nonneg (fun y => abs_nonneg (f y))) measureReal_nonneg) x
  · simp only [finiteFunctionMaximal, dite_eq_right h, le_refl]

/-- Enlarging the finite family cannot decrease the maximum. -/
theorem finiteFunctionMaximal_mono
    (G H : Finset (∀ i, Box (Fin (d i)))) (hGH : G ⊆ H)
    (f : ProductPoint d → ℝ) (x : ProductPoint d) :
    finiteFunctionMaximal G f x ≤ finiteFunctionMaximal H f x := by
  by_cases h : G.Nonempty
  · rw [finiteFunctionMaximal, dite_eq_left h]
    exact Finset.sup'_le _ _
      (fun Q hQ => positiveMean_le_finiteFunctionMaximal H f Q (hGH hQ) x)
  · simpa only [finiteFunctionMaximal, dite_eq_right h] using
      finiteFunctionMaximal_nonneg H f x

/-- The finite maximum vanishes outside all rectangles in its family. -/
theorem finiteFunctionMaximal_eq_zero_of_outside
    (G : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ)
    (x : ProductPoint d) (hx : ∀ Q ∈ G, x ∉ productRectangle Q) :
    finiteFunctionMaximal G f x = 0 := by
  by_cases h : G.Nonempty
  · rw [finiteFunctionMaximal, dite_eq_left h]
    apply Finset.sup'_eq_of_forall
    intro Q hQ
    exact Set.indicator_of_notMem (hx Q hQ) _
  · simp only [finiteFunctionMaximal, dite_eq_right h]

/-- A finite maximum of supported constant means is measurable for every input. -/
theorem measurable_finiteFunctionMaximal
    (G : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ) :
    Measurable (finiteFunctionMaximal G f) := by
  by_cases h : G.Nonempty
  · have hm := Finset.measurable_sup' (s := G) h
      (fun Q _ => (measurable_const : Measurable (fun _ : ProductPoint d =>
        (∫ y in productRectangle Q, |f y|) / volume.real (productRectangle Q))).indicator
          (measurableSet_productRectangle Q))
    convert hm using 1
    funext x
    rw [finiteFunctionMaximal, dite_eq_left h, Finset.sup'_apply]
  · have hz : finiteFunctionMaximal G f = (fun _ => 0) := by
      funext x
      simp only [finiteFunctionMaximal, dite_eq_right h]
    rw [hz]
    exact measurable_const

/-- A finite maximum has integrable positive real powers. -/
theorem integrable_rpow_finiteFunctionMaximal
    (G : Finset (∀ i, Box (Fin (d i)))) (f : ProductPoint d → ℝ)
    (p : ℝ) (hp : 0 < p) :
    Integrable (fun x => Real.rpow (finiteFunctionMaximal G f x) p) volume := by
  let b (Q : ∀ i, Box (Fin (d i))) : ProductPoint d → ℝ :=
    (productRectangle Q).indicator (fun _ =>
      |Real.rpow ((∫ y in productRectangle Q, |f y|) / volume.real (productRectangle Q)) p|)
  have hb (Q : ∀ i, Box (Fin (d i))) : Integrable (b Q) volume :=
    (integrableOn_const (productRectangle_volume_lt_top Q).ne).integrable_indicator
      (measurableSet_productRectangle Q)
  have hb0 (Q : ∀ i, Box (Fin (d i))) (x : ProductPoint d) : 0 ≤ b Q x :=
    Set.indicator_nonneg (fun _ _ => abs_nonneg _) x
  have hi := integrable_finsetSum G (fun Q _ => hb Q)
  apply hi.mono'
  · exact ((Real.continuous_rpow_const hp.le).measurable.comp
      (measurable_finiteFunctionMaximal G f)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs]
    by_cases h : G.Nonempty
    · obtain ⟨Q, hQ, hmax⟩ := Finset.exists_mem_eq_sup' h
        (fun Q => (productRectangle Q).indicator
          (fun _ => (∫ y in productRectangle Q, |f y|) / volume.real (productRectangle Q)) x)
      rw [finiteFunctionMaximal, dite_eq_left h, hmax]
      by_cases hxQ : x ∈ productRectangle Q
      · rw [Set.indicator_of_mem hxQ]
        simpa only [b, Set.indicator_of_mem hxQ] using
          Finset.single_le_sum (fun R _ => hb0 R x) hQ
      · rw [Set.indicator_of_notMem hxQ]
        simpa only [Real.rpow_eq_pow, Real.zero_rpow hp.ne', abs_zero] using
          Finset.sum_nonneg (fun R (_ : R ∈ G) => hb0 R x)
    · rw [finiteFunctionMaximal, dite_eq_right h]
      simpa only [Real.rpow_eq_pow, Real.zero_rpow hp.ne', abs_zero] using
        Finset.sum_nonneg (fun R (_ : R ∈ G) => hb0 R x)

private theorem productRectangle_subset_of_coordinates
    {Q R : ∀ i, Box (Fin (d i))} (hQR : ∀ i, Q i ≤ R i) :
    productRectangle Q ⊆ productRectangle R := by
  intro x hx
  exact (mem_productRectangle R x).mpr (fun i => hQR i ((mem_productRectangle Q x).mp hx i))

private theorem raw_maximal_on_forest_root
    (T G : Finset (∀ i, Box (Fin (d i))))
    (hdis : Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (productRectangle R) (productRectangle S)))
    (hcover : ∀ Q ∈ G, ∃ R ∈ T, ∀ i, Q i ≤ R i)
    (R : ∀ i, Box (Fin (d i))) (hR : R ∈ T)
    (f : ProductPoint d → ℝ) (x : ProductPoint d) (hx : x ∈ productRectangle R) :
    finiteFunctionMaximal G f x =
      finiteFunctionMaximal (G.filter (fun Q => ∀ i, Q i ≤ R i)) f x := by
  apply le_antisymm
  · by_cases hG : G.Nonempty
    · rw [finiteFunctionMaximal, dite_eq_left hG]
      apply Finset.sup'_le
      intro Q hQ
      by_cases hQR : ∀ i, Q i ≤ R i
      · exact positiveMean_le_finiteFunctionMaximal _ f Q
          (Finset.mem_filter.mpr ⟨hQ, hQR⟩) x
      · obtain ⟨S, hS, hQS⟩ := hcover Q hQ
        have hSR : S ≠ R := by
          intro h
          subst S
          exact hQR hQS
        have hxQ : x ∉ productRectangle Q := by
          intro hxQ
          exact Set.disjoint_left.mp (hdis hS hR hSR)
            (productRectangle_subset_of_coordinates hQS hxQ) hx
        rw [Set.indicator_of_notMem hxQ]
        exact finiteFunctionMaximal_nonneg _ f x
    · simpa only [finiteFunctionMaximal, dite_eq_right hG] using
        finiteFunctionMaximal_nonneg (G.filter (fun Q => ∀ i, Q i ≤ R i)) f x
  · exact finiteFunctionMaximal_mono _ G (Finset.filter_subset _ _) f x

private theorem raw_maximal_zero_off_forest
    (T G : Finset (∀ i, Box (Fin (d i))))
    (hcover : ∀ Q ∈ G, ∃ R ∈ T, ∀ i, Q i ≤ R i)
    (f : ProductPoint d → ℝ) (x : ProductPoint d)
    (hx : x ∉ ⋃ R ∈ T, productRectangle R) : finiteFunctionMaximal G f x = 0 := by
  apply finiteFunctionMaximal_eq_zero_of_outside
  intro Q hQ hxQ
  obtain ⟨R, hR, hQR⟩ := hcover Q hQ
  exact hx (Set.mem_iUnion₂.mpr
    ⟨R, hR, productRectangle_subset_of_coordinates hQR hxQ⟩)

/-- A finite family contained in pairwise disjoint top rectangles localizes
pointwise to its containment filters. -/
theorem finiteFunctionMaximal_forest
    (T G : Finset (∀ i, Box (Fin (d i))))
    (hdis : Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (productRectangle R) (productRectangle S)))
    (hcover : ∀ Q ∈ G, ∃ R ∈ T, ∀ i, Q i ≤ R i)
    (f : ProductPoint d → ℝ) (x : ProductPoint d) :
    finiteFunctionMaximal G f x =
      ∑ R ∈ T, finiteFunctionMaximal
        (G.filter (fun Q => ∀ i, Q i ≤ R i)) f x := by
  by_cases hx : ∃ R ∈ T, x ∈ productRectangle R
  · obtain ⟨R, hR, hxR⟩ := hx
    calc
      _ = finiteFunctionMaximal (G.filter (fun Q => ∀ i, Q i ≤ R i)) f x :=
        raw_maximal_on_forest_root T G hdis hcover R hR f x hxR
      _ = _ := by
        symm
        apply Finset.sum_eq_single R
        · intro S hS hSR
          apply finiteFunctionMaximal_eq_zero_of_outside
          intro Q hQ hxQ
          exact Set.disjoint_left.mp (hdis hS hR hSR)
            (productRectangle_subset_of_coordinates (Finset.mem_filter.mp hQ).2 hxQ) hxR
        · exact fun h => False.elim (h hR)
  · have hzero : finiteFunctionMaximal G f x = 0 :=
      raw_maximal_zero_off_forest T G hcover f x
        (by
          intro h
          obtain ⟨R, hR, hxR⟩ := Set.mem_iUnion₂.mp h
          exact hx ⟨R, hR, hxR⟩)
    rw [hzero]
    symm
    apply Finset.sum_eq_zero
    intro R hR
    apply finiteFunctionMaximal_eq_zero_of_outside
    intro Q hQ hxQ
    exact hx ⟨R, hR,
      productRectangle_subset_of_coordinates (Finset.mem_filter.mp hQ).2 hxQ⟩

/-- The power integral splits over the disjoint top rectangles. -/
theorem integral_rpow_finiteFunctionMaximal_forest
    (T G : Finset (∀ i, Box (Fin (d i))))
    (hdis : Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
      (fun R S => Disjoint (productRectangle R) (productRectangle S)))
    (hcover : ∀ Q ∈ G, ∃ R ∈ T, ∀ i, Q i ≤ R i)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 0 < p) :
    (∫ x, Real.rpow (finiteFunctionMaximal G f x) p) =
      ∑ R ∈ T, ∫ x in productRectangle R,
        Real.rpow (finiteFunctionMaximal
          (G.filter (fun Q => ∀ i, Q i ≤ R i)) f x) p := by
  have hi := integrable_rpow_finiteFunctionMaximal G f p hp
  calc
    _ = ∫ x in ⋃ R ∈ T, productRectangle R,
        Real.rpow (finiteFunctionMaximal G f x) p := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      simp only [raw_maximal_zero_off_forest T G hcover f x hx,
        Real.rpow_eq_pow, Real.zero_rpow hp.ne']
    _ = ∑ R ∈ T, ∫ x in productRectangle R,
        Real.rpow (finiteFunctionMaximal G f x) p :=
      integral_biUnion_finset T (fun R _ => measurableSet_productRectangle R) hdis
        (fun _ _ => hi.integrableOn)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro R hR
      apply setIntegral_congr_fun (measurableSet_productRectangle R)
      intro x hx
      exact congrArg (fun a : ℝ => Real.rpow a p)
        (raw_maximal_on_forest_root T G hdis hcover R hR f x hx)

end ReyZygmund
