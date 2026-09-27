import ReyZygmund.Maximal.SetEndpointLimit
import ReyZygmund.Overlap.SetMoments
import ReyZygmund.Overlap.SetMomentLimits

/-! # From the endpoint estimate to sparse overlap

This proves the implication used for sparse Phi-Zygmund families. Sets may be
unbounded and the overlap countable. The constants are `D = 8 * exp 2 * A * k!`
and exponential factor three. Bounded tests suffice for the weak hypothesis; the
last formulation assumes the endpoint bound for every measurable input.

-/

open MeasureTheory
open scoped ENNReal Classical

namespace ReyZygmund.Overlap

variable {d : ℕ}

private theorem endpoint_coefficient_ge_one (k : ℕ) (A : ℝ) (hA : 1 ≤ A) :
    1 ≤ 8 * A * Real.exp 2 * (k.factorial : ℝ) := by
  have hfact : 1 ≤ (k.factorial : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos k))
  have h8A : 1 ≤ 8 * A := by linarith
  have he : 1 ≤ Real.exp (2 : ℝ) := Real.one_le_exp (by norm_num)
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le h8A he) hfact

private theorem finite_set_endpoint_uniform
    (H : Finset (Set (Fin d → ℝ))) (hm : ∀ I ∈ H, MeasurableSet I)
    (hpos : ∀ I ∈ H, 0 < volume I) (hfin : ∀ I ∈ H, volume I < ∞)
    (k : ℕ) (A : ℝ) (hA : 1 ≤ A)
    (hweak : ∀ h : (Fin d → ℝ) → ℝ,
      Measurable h → (∀ x, 0 ≤ h x) → (∃ B : ℝ, ∀ x, h x ≤ B) →
      Bornology.IsBounded (Function.support h) → ∀ t : ℝ, 0 < t →
        volume {x | ENNReal.ofReal t < setFamilyMaximal (H : Set _) h x} ≤
          ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
            (|h x| / t * (Real.log (Real.exp 1 + |h x| / t)) ^ k))
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f)
    (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
    (∫⁻ x, (setFamilyMaximal (H : Set _) f x) ^ p) ≤
      (ENNReal.ofReal (8 * A * Real.exp 2 * (k.factorial : ℝ) /
        (p - 1) ^ (k + 1))) ^ p * ∫⁻ x, (ENNReal.ofReal |f x|) ^ p := by
  let D := 8 * A * Real.exp 2 * (k.factorial : ℝ)
  have hD : 1 ≤ D := endpoint_coefficient_ge_one k A hA
  have heps : 0 < p - 1 := sub_pos.mpr hp
  have hden : 0 < (p - 1) ^ (k + 1) := pow_pos heps _
  have hden1 : (p - 1) ^ (k + 1) ≤ 1 :=
    pow_le_one₀ heps.le (by linarith)
  have hratio : 1 ≤ D / (p - 1) ^ (k + 1) :=
    (le_div_iff₀ hden).mpr (by simpa only [one_mul] using hden1.trans hD)
  have hpow : D / (p - 1) ^ (k + 1) ≤
      (D / (p - 1) ^ (k + 1)) ^ p :=
    Real.self_le_rpow_of_one_le hratio hp.le
  apply (finite_set_endpoint_maximal_power H hm hpos hfin k A hA hweak f hf p hp hp2).trans
  apply mul_le_mul' _ le_rfl
  change ENNReal.ofReal (D / (p - 1) ^ (k + 1)) ≤
    (ENNReal.ofReal (D / (p - 1) ^ (k + 1))) ^ p
  simpa only [ENNReal.ofReal_rpow_of_nonneg (zero_le_one.trans hratio)
    (zero_lt_one.trans hp).le] using ENNReal.ofReal_le_ofReal hpow

/-- The complete implication from bounded measurable endpoint tests. It
includes all real moment orders, the exact exponential constant and a proof
that the real overlap representative agrees with the series a.e. -/
theorem set_endpoint_sparse_overlap_from_bounded_tests
    (E : Set (Set (Fin d → ℝ))) (hE : E.Countable)
    (hm : ∀ I ∈ E, MeasurableSet I) (hpos : ∀ I ∈ E, 0 < volume I)
    (hfin : ∀ I ∈ E, volume I < ∞) (k : ℕ) (A : ℝ) (hA : 1 ≤ A)
    (hweak : ∀ f : (Fin d → ℝ) → ℝ,
      Measurable f → (∀ x, 0 ≤ f x) → (∃ B : ℝ, ∀ x, f x ≤ B) →
      Bornology.IsBounded (Function.support f) → ∀ t : ℝ, 0 < t →
        volume {x | ENNReal.ofReal t < setFamilyMaximal E f x} ≤
          ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
            (|f x| / t * (Real.log (Real.exp 1 + |f x| / t)) ^ k))
    (G : Set (Set (Fin d → ℝ))) (hGE : G ⊆ E)
    (eta : ℝ) (heta : 0 < eta) (_heta1 : eta ≤ 1)
    (W : Set (Fin d → ℝ) → Set (Fin d → ℝ))
    (hWm : ∀ I ∈ G, MeasurableSet (W I)) (hWs : ∀ I ∈ G, W I ⊆ I)
    (hWd : Set.Pairwise G (fun I J => Disjoint (W I) (W J)))
    (hWv : ∀ I ∈ G, ENNReal.ofReal eta * volume I ≤ volume (W I))
    (hshadow : volume (setShadow G) < ∞) :
    let D := 8 * A * Real.exp 2 * (k.factorial : ℝ)
    (∀ᵐ x ∂volume, setOverlap G x < ∞) ∧
      (∀ q : ℝ, 1 ≤ q →
        eLpNorm (fun x => (setOverlap G x).toReal) (ENNReal.ofReal q) volume ≤
          ENNReal.ofReal ((D / eta) * q ^ (k + 1)) *
            (volume (setShadow G)) ^ (1 / q)) ∧
      (∫⁻ x in setShadow G, ENNReal.ofReal
        (Real.exp ((1 / 2 : ℝ) * (eta * (setOverlap G x).toReal /
          (Real.exp 1 * D)) ^ (1 / ((k + 1 : ℕ) : ℝ))))) ≤
            3 * volume (setShadow G) := by
  let D := 8 * A * Real.exp 2 * (k.factorial : ℝ)
  let B := D / eta
  have hD : 0 < D := zero_lt_one.trans_le (endpoint_coefficient_ge_one k A hA)
  have hB : 0 < B := div_pos hD heta
  have hc : G.Countable := hE.mono hGE
  have hmG : ∀ I ∈ G, MeasurableSet I := fun I hI => hm I (hGE hI)
  have hhigh (q : ℝ) (hq : 2 ≤ q) :
      (∫⁻ x, (setOverlap G x) ^ q) ≤
        (ENNReal.ofReal (B * (q - 1) ^ (k + 1))) ^ q * volume (setShadow G) := by
    apply countable_set_moment_of_finite G hc hmG q
      (lt_of_lt_of_le (by norm_num) hq)
    intro H
    let F := H.image Subtype.val
    have hFG : ∀ I ∈ F, I ∈ G := by
      intro I hI
      obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hI
      exact J.2
    have hFM : ∀ I ∈ F, MeasurableSet I := fun I hI => hmG I (hFG I hI)
    have hFP : ∀ I ∈ F, 0 < volume I := fun I hI => hpos I (hGE (hFG I hI))
    have hFF : ∀ I ∈ F, volume I < ∞ := fun I hI => hfin I (hGE (hFG I hI))
    have hsubmax (f : (Fin d → ℝ) → ℝ) (x) :
        setFamilyMaximal (F : Set _) f x ≤ setFamilyMaximal E f x := by
      apply iSup_le
      intro I
      exact le_iSup_of_le (⟨I.1, hGE (hFG I.1 I.2)⟩ : E) le_rfl
    have hweakF (f : (Fin d → ℝ) → ℝ) (hf : Measurable f)
        (hn : ∀ x, 0 ≤ f x) (hb : ∃ B : ℝ, ∀ x, f x ≤ B)
        (hs : Bornology.IsBounded (Function.support f)) (t : ℝ) (ht : 0 < t) :
        volume {x | ENNReal.ofReal t < setFamilyMaximal (F : Set _) f x} ≤
          ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
            (|f x| / t * (Real.log (Real.exp 1 + |f x| / t)) ^ k) := by
      apply (measure_mono (fun x hx => hx.trans_le (hsubmax f x))).trans
      exact hweak f hf hn hb hs t ht
    have hstrong (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (_hn : ∀ x, 0 ≤ f x)
        (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
        (∫⁻ x, (setFamilyMaximal (F : Set _) f x) ^ p) ≤
          (ENNReal.ofReal (D / (p - 1) ^ (k + 1))) ^ p *
            ∫⁻ x, (ENNReal.ofReal |f x|) ^ p :=
      finite_set_endpoint_uniform F hFM hFP hFF k A hA hweakF f hf p hp hp2
    have hh := finite_set_sparse_overlap_lintegral F hFM hFP hFF eta heta W
      (fun I hI => hWm I (hFG I hI)) (fun I hI => hWs I (hFG I hI))
      (fun I hI J hJ hne => hWd (hFG I hI) (hFG J hJ) hne)
      (fun I hI => hWv I (hFG I hI)) (k + 1) D hD hstrong q hq
    simpa only [B, div_eq_mul_inv] using hh
  have hexp := set_overlap_exponential_of_high_moments G hc hmG hshadow
    (k + 1) (by omega) B hB hhigh
  refine ⟨hexp.1, ?_, ?_⟩
  · intro q hq
    exact set_overlap_eLpNorm_of_high_moments G hc hmG hshadow
      (k + 1) B hB.le hhigh q hq
  · have heq (x : Fin d → ℝ) :
        (setOverlap G x).toReal / (Real.exp 1 * B) =
          eta * (setOverlap G x).toReal / (Real.exp 1 * D) := by
      dsimp only [B]
      field_simp [heta.ne', hD.ne', Real.exp_ne_zero 1]
    simpa only [heq] using hexp.2

/-- The endpoint-to-overlap implication with the endpoint hypothesis for every
measurable input. Neither the sets nor the inputs need be bounded. -/
theorem set_endpoint_sparse_overlap
    (E : Set (Set (Fin d → ℝ))) (hE : E.Countable)
    (hm : ∀ I ∈ E, MeasurableSet I) (hpos : ∀ I ∈ E, 0 < volume I)
    (hfin : ∀ I ∈ E, volume I < ∞) (k : ℕ) (A : ℝ) (hA : 1 ≤ A)
    (hweak : ∀ f : (Fin d → ℝ) → ℝ, Measurable f → ∀ t : ℝ, 0 < t →
      volume {x | ENNReal.ofReal t < setFamilyMaximal E f x} ≤
        ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
          (|f x| / t * (Real.log (Real.exp 1 + |f x| / t)) ^ k))
    (G : Set (Set (Fin d → ℝ))) (hGE : G ⊆ E)
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (W : Set (Fin d → ℝ) → Set (Fin d → ℝ))
    (hWm : ∀ I ∈ G, MeasurableSet (W I)) (hWs : ∀ I ∈ G, W I ⊆ I)
    (hWd : Set.Pairwise G (fun I J => Disjoint (W I) (W J)))
    (hWv : ∀ I ∈ G, ENNReal.ofReal eta * volume I ≤ volume (W I))
    (hshadow : volume (setShadow G) < ∞) :
    let D := 8 * A * Real.exp 2 * (k.factorial : ℝ)
    (∀ᵐ x ∂volume, setOverlap G x < ∞) ∧
      (∀ q : ℝ, 1 ≤ q →
        eLpNorm (fun x => (setOverlap G x).toReal) (ENNReal.ofReal q) volume ≤
          ENNReal.ofReal ((D / eta) * q ^ (k + 1)) *
            (volume (setShadow G)) ^ (1 / q)) ∧
      (∫⁻ x in setShadow G, ENNReal.ofReal
        (Real.exp ((1 / 2 : ℝ) * (eta * (setOverlap G x).toReal /
          (Real.exp 1 * D)) ^ (1 / ((k + 1 : ℕ) : ℝ))))) ≤
            3 * volume (setShadow G) := by
  exact set_endpoint_sparse_overlap_from_bounded_tests E hE hm hpos hfin k A hA
    (fun f hf _ _ _ t ht => hweak f hf t ht) G hGE eta heta heta1 W hWm hWs hWd hWv hshadow

end ReyZygmund.Overlap
