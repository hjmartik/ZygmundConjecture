import ReyZygmund.MathlibOnly.Definitions
import ReyZygmund.MathlibOnly.Proof.MeasureBridge
import ReyZygmund.MathlibOnly.Proof.FamilyBridge
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# From the independent definitions to the proof library

The grid conversion keeps every cube and scale. The maximal functions agree
pointwise: an average contributes precisely at points of its rectangle.
Almost-everywhere finiteness identifies the extended norms and exponential
integrals with the real-valued quantities used in the analytic proofs.
-/

open BoxIntegral MeasureTheory Filter
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.MathlibOnly

noncomputable section

/-- The same grid, with nesting expressed through the box order. -/
def CubeGrid.toProof {d : ℕ} (D : CubeGrid d) : Proof.CubeGrid d where
  cubes := D.cubes
  side_length := D.side_length
  pairwise_disjoint := D.pairwise_disjoint
  covers := D.covers
  nested := D.nested

theorem gridRectangles_eq_proof {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, CubeGrid (d i)) :
    gridRectangles D = Proof.gridRectangles (fun i => (D i).toProof) := rfl

theorem phiRectangles_eq_proof {n : ℕ} {d : Fin (n + 1) → ℕ}
    (D : ∀ i, CubeGrid (d i)) (Phi : (Fin n → ℤ) → ℤ) :
    phiRectangles D Phi = Proof.phiRectangles (fun i => (D i).toProof) Phi := rfl

theorem weaklyIncomparable_iff_proof {m : ℕ} {d : Fin m → ℕ}
    (G : Set (Rectangle d)) :
    WeaklyIncomparable G ↔ Proof.Estimates.WeaklyIncomparable G := Iff.rfl

theorem sparse_iff_proof {m : ℕ} {d : Fin m → ℕ} (eta : ℝ)
    (G : Set (Rectangle d)) : Sparse eta G ↔ Proof.Estimates.Sparse eta G := Iff.rfl

theorem shadow_eq_proof {m : ℕ} {d : Fin m → ℕ} (G : Set (Rectangle d)) :
    shadow G = Proof.shadow G := rfl

theorem overlap_eq_proof {m : ℕ} {d : Fin m → ℕ} (G : Set (Rectangle d)) :
    overlap G = Proof.overlap G := rfl

theorem continuousRectangles_eq_proof {n : ℕ} (d : Fin (n + 1) → ℕ)
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) :
    continuousRectangles d phi = Proof.continuousRectangles d phi := rfl

theorem roundedRectangles_eq_proof {n : ℕ} {d : Fin (n + 1) → ℕ}
    (tau : ∀ i, Fin (d i) → Fin 3)
    (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)) :
    roundedRectangles tau phi = Proof.roundedRectangles tau phi := rfl

private theorem supremum_containing_eq_indicator {α β : Type*}
    (G : Set α) (sets : α → Set β) (average : α → ℝ≥0∞) (x : β) :
    (⨆ R ∈ G, ⨆ (_ : x ∈ sets R), average R) =
      ⨆ R : G, (sets R.1).indicator (fun _ => average R.1) x := by
  apply le_antisymm
  · refine iSup_le fun R => iSup_le fun hR => iSup_le fun hx => ?_
    calc
      average R = (sets R).indicator (fun _ => average R) x :=
        (Set.indicator_of_mem hx (fun _ : β => average R)).symm
      _ ≤ ⨆ R : G, (sets R.1).indicator (fun _ => average R.1) x :=
        le_iSup (fun S : G => (sets S.1).indicator (fun _ => average S.1) x) ⟨R, hR⟩
  · refine iSup_le fun R => ?_
    by_cases hx : x ∈ sets R.1
    · rw [Set.indicator_of_mem hx]
      exact le_iSup_of_le R.1 (le_iSup_of_le R.2 (le_iSup_of_le hx le_rfl))
    · rw [Set.indicator_of_notMem hx]
      exact bot_le

/-- Restricting the supremum to rectangles containing the point gives the
same maximal function as supporting each average on its rectangle. -/
theorem maximal_eq_proof {m : ℕ} {d : Fin m → ℕ}
    (G : Set (Rectangle d)) (f : Point d → ℝ) : maximal G f = Proof.maximal G f := by
  funext x
  exact supremum_containing_eq_indicator G rectangle
    (fun R => (∫⁻ y in rectangle R, ENNReal.ofReal |f y| ∂volume) /
      volume (rectangle R)) x

theorem maximalIco_eq_proof {m : ℕ} {d : Fin m → ℕ}
    (G : Set (Rectangle d)) (f : Point d → ℝ) :
    maximalIco G f = Proof.Estimates.maximalIco G f := by
  funext x
  exact supremum_containing_eq_indicator G rectangleIco
    (fun R => (∫⁻ y in rectangleIco R, ENNReal.ofReal |f y| ∂volume) /
      volume (rectangleIco R)) x

/-- An almost-everywhere finite nonnegative function has the same norm as
its real-valued representative, including when the norm is infinite. -/
theorem eLpNorm_eq_toReal {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ≥0∞} (p : ℝ≥0∞)
    (hf : ∀ᵐ x ∂μ, f x < ∞) :
    eLpNorm f p μ = eLpNorm (fun x => (f x).toReal) p μ := by
  calc
    eLpNorm f p μ = eLpNorm (ENNReal.ofReal ∘ fun x => (f x).toReal) p μ := by
      apply eLpNorm_congr_ae
      filter_upwards [hf] with x hx
      exact (ENNReal.ofReal_toReal hx.ne).symm
    _ = eLpNorm (fun x => (f x).toReal) p μ :=
      eLpNorm_ofReal _ (.of_forall fun _ => ENNReal.toReal_nonneg)

theorem exp_ofReal {t : ℝ} (ht : 0 ≤ t) :
    exp (ENNReal.ofReal t) = ENNReal.ofReal (Real.exp t) := by
  simp only [exp, EReal.coe_ennreal_ofReal, max_eq_left (by exact_mod_cast ht),
    EReal.exp_coe]

/-- For finite nonnegative inputs the extended power and exponential agree
with the real expressions used in the overlap proof. -/
theorem exp_mul_rpow_eq {t : ℝ≥0∞} (ht : t < ∞)
    {c a beta : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hbeta : 0 ≤ beta) :
    exp (ENNReal.ofReal c * (ENNReal.ofReal a * t) ^ beta) =
      ENNReal.ofReal (Real.exp (c * Real.rpow (a * t.toReal) beta)) := by
  have hbase : ENNReal.ofReal a * t = ENNReal.ofReal (a * t.toReal) := by
    rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_toReal ht.ne]
  rw [hbase, ENNReal.ofReal_rpow_of_nonneg
    (mul_nonneg ha ENNReal.toReal_nonneg) hbeta,
    ← ENNReal.ofReal_mul hc]
  exact exp_ofReal (mul_nonneg hc (Real.rpow_nonneg
    (mul_nonneg ha ENNReal.toReal_nonneg) _))

theorem lintegral_exp_mul_rpow_eq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (s : Set α) {f : α → ℝ≥0∞}
    (hf : ∀ᵐ x ∂μ, f x < ∞) {c a beta : ℝ}
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hbeta : 0 ≤ beta) :
    (∫⁻ x in s, exp (ENNReal.ofReal c * (ENNReal.ofReal a * f x) ^ beta) ∂μ) =
      ∫⁻ x in s, ENNReal.ofReal (Real.exp (c * Real.rpow (a * (f x).toReal) beta))
        ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hf] with x hx
  exact exp_mul_rpow_eq hx hc ha hbeta

/-- For finite families, the real overlap is exactly the finite indicator sum. -/
theorem overlap_toReal_finset {m : ℕ} {d : Fin m → ℕ}
    (G : Finset (Rectangle d)) (x : Point d) :
    (overlap (G : Set (Rectangle d)) x).toReal =
      ∑ R ∈ G, (rectangle R).indicator (fun _ => (1 : ℝ)) x := by
  change (Proof.overlap (G : Set (Rectangle d)) x).toReal = _
  rw [Proof.Estimates.overlap_eq, Overlap.toReal_overlap_finset]
  simp only [Overlap.finiteOverlap, ← Proof.rectangle_eq_flat]
  rfl

end
end ReyZygmund.MathlibOnly
