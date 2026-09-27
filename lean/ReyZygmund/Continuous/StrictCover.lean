import ReyZygmund.Continuous.Cover

/-! The strict volume comparison for the continuous covering argument. Positive total
dimension is necessary: both volumes equal one in dimension zero. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Continuous

open Geometry

private theorem box_volume_lt_of_width_lt {k : ℕ} (hk : 0 < k)
    (R I : Box (Fin k))
    (hwidth : ∀ j, I.upper j - I.lower j < 8 * (R.upper j - R.lower j)) :
    volume.real (I : Set (Fin k → ℝ)) <
      (8 : ℝ) ^ k * volume.real (R : Set (Fin k → ℝ)) := by
  let : NeZero k := ⟨ne_of_gt hk⟩
  simp only [measureReal_def, Box.volume_apply']
  calc
    Finset.univ.prod (fun j : Fin k => I.upper j - I.lower j) <
        Finset.univ.prod (fun j : Fin k => 8 * (R.upper j - R.lower j)) :=
      Finset.prod_lt_prod_of_nonempty₀
        (fun j _ => sub_pos.mpr (I.lower_lt_upper j))
        (fun j _ => hwidth j) Finset.univ_nonempty
    _ = (8 : ℝ) ^ k * Finset.univ.prod (fun j : Fin k => R.upper j - R.lower j) := by
      rw [Finset.prod_mul_distrib]
      simp

/-- Prescribed-shift cover with the paper's strict dimensional
volume loss, not just the weak bound sufficient for maximal domination. -/
theorem continuous_rectangle_strict_cover {n : ℕ} {d : Fin (n + 1) → ℕ}
    (hdim : 0 < ∑ i, d i)
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ))
    (R : ∀ i, Box (Fin (d i))) (hR : R ∈ continuousPhiRectangles d phi) :
    ∃ (tau : ∀ i, Fin (d i) → Fin 3) (I : ∀ i, Box (Fin (d i))),
      I ∈ roundedGridRectangles (fun i => shiftedDyadicGrid (d i) (tau i)) phi ∧
      (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ⊆ flatProductBox I ∧
      volume.real (flatProductBox I : Set (Fin (∑ i, d i) → ℝ)) /
          volume.real (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) <
        (8 : ℝ) ^ (∑ i, d i) := by
  obtain ⟨s, hwidth⟩ := hR
  let side : Fin (n + 1) → ℝ := Fin.snoc (fun j => (s j).1) (phi s).1
  have hside (i : Fin (n + 1)) : 0 < side i := by
    exact Fin.lastCases (by simpa only [side, Fin.snoc_last, Set.mem_Ioi] using (phi s).2)
      (fun j => by simpa only [side, Fin.snoc_castSucc, Set.mem_Ioi] using (s j).2) i
  have hcover (i : Fin (n + 1)) :=
    prescribed_dyadic_cover (R i) (side i) (hside i) (hwidth i)
  choose tau I hgrid hsub hwidthI using hcover
  refine ⟨tau, I, ?_, ?_, ?_⟩
  · refine ⟨fun i => roundedScale (side i), ?_, hgrid⟩
    refine ⟨s, ?_⟩
    funext i
    exact Fin.lastCases (by simp [side]) (fun j => by simp [side]) i
  · intro x hx
    obtain ⟨y, rfl⟩ := (flattenCoordinates d).surjective x
    change flattenCoordinates d y ∈ flatProductBox R at hx
    change flattenCoordinates d y ∈ flatProductBox I
    rw [mem_flatProductBox, mem_productBox] at hx ⊢
    exact fun i => hsub i (Box.coe_subset_Icc (hx i))
  · apply (div_lt_iff₀ (box_volume_pos (flatProductBox R))).mpr
    apply box_volume_lt_of_width_lt hdim (flatProductBox R) (flatProductBox I)
    intro j
    obtain ⟨⟨i, a⟩, rfl⟩ := (finSigmaFinEquiv (n := d)).surjective j
    simp only [flatProductBox, flattenCoordinates_apply]
    rw [hwidthI i a, hwidth i a]
    exact (roundedScale_bounds (hside i)).2

end ReyZygmund.Continuous
