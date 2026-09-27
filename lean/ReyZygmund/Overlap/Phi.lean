import ReyZygmund.Continuous.DyadicEndpoint
import ReyZygmund.Maximal.EndpointFinite
import ReyZygmund.Overlap.EndpointMoments
import ReyZygmund.Overlap.EndpointGlobal

/-! # Sparse overlap for monotone side relations

The endpoint constant is chosen before the grids and side function. The
finite sparse estimate then passes to the countable overlap. No
incomparability assumption is used in this branch of the argument.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

namespace ReyZygmund.Overlap

open Geometry ReyZygmund.Continuous

theorem phi_sparse_overlap_moments :
    ∀ (n totalDim : ℕ), 2 ≤ n →
    ∃ K : ℝ, 0 < K ∧
    ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
    ∀ (D : ∀ i, DyadicGrid (d i)) (Phi : (Fin n → ℤ) → ℤ), Monotone Phi →
    ∀ (G : Set (∀ i, Box (Fin (d i)))), G ⊆ dyadicPhiRectangles D Phi →
    ∀ (eta : ℝ), 0 < eta →
    ∀ E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ),
    (∀ R ∈ G, MeasurableSet (E R)) →
    (∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) →
    Set.Pairwise G (fun R S => Disjoint (E R) (E S)) →
    (∀ R ∈ G, ENNReal.ofReal eta *
      volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤ volume (E R)) →
    ∀ q : ℝ, 2 ≤ q →
      (∫⁻ x, (overlap G x) ^ q) ≤
        (ENNReal.ofReal (K * eta⁻¹ * q ^ n)) ^ q * volume (shadow G) := by
  intro n totalDim hn
  obtain ⟨A, hA, hendpoint⟩ := dyadic_phi_endpoint_theorem n totalDim hn
  let K : ℝ := max 1 (8 * A * Real.exp 2 * ((n - 1).factorial : ℝ))
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  intro d hd hdim D Phi hPhi G hG eta heta E hEm hEs hEd hEv q hq
  have hgrid : G ⊆ gridRectangles D := by
    intro R hR i
    obtain ⟨a, ha⟩ := hG hR
    exact ⟨_, ha i⟩
  have hc : G.Countable := (countable_gridRectangles D).mono hgrid
  apply countable_overlap_lintegral_of_finite G hc n (K * eta⁻¹) ?_ q hq
  intro H r hr
  let F := H.image Subtype.val
  have hFG : ∀ R ∈ F, R ∈ G := by
    intro R hR
    obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp hR
    exact S.2
  have hweak (g : (Fin (∑ i, d i) → ℝ) → ℝ)
      (hg : LocallyIntegrable g volume) (t : ℝ) (ht : 0 < t) :
      volume {x | ENNReal.ofReal t < euclideanFamilyMaximal (F : Set _) g x} ≤
        ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal
          (|g x| / t * (Real.log (Real.exp 1 + |g x| / t)) ^ (n - 1)) := by
    apply le_trans (measure_mono ?_)
      (by simpa using hendpoint d hd hdim D Phi hPhi g hg t ht)
    intro x hx
    change ENNReal.ofReal t < euclideanFamilyMaximal (F : Set _) g x at hx
    change ENNReal.ofReal t < euclideanFamilyMaximal (dyadicPhiRectangles D Phi) g x
    apply hx.trans_le
    unfold euclideanFamilyMaximal
    apply iSup_le
    intro R
    exact le_iSup_of_le (⟨R.1, hG (hFG R.1 R.2)⟩ : dyadicPhiRectangles D Phi) le_rfl
  apply finite_endpoint_sparse_overlap_lintegral F eta heta E
    (fun R hR => hEm R (hFG R hR))
    (fun R hR => hEs R (hFG R hR))
    (fun R hR S hS hne => hEd (hFG R hR) (hFG S hS) hne)
    (fun R hR => hEv R (hFG R hR)) n K hK ?_ r hr
  intro f hf hm hnn p hp hp2
  have h := finite_endpoint_maximal_power_uniform F (n - 1) A hA.le hweak
    f hf hm hnn p hp hp2
  simpa only [K, show n - 1 + 1 = n by omega, Real.rpow_eq_pow] using h

/-- The full countable sparse-Phi estimate, with constants independent of
the grids, the monotone side function and the family. -/
theorem phi_sparse_overlap_exponential :
    ∀ (n totalDim : ℕ), 2 ≤ n →
    ∀ eta : ℝ, 0 < eta →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (d : Fin (n + 1) → ℕ), (∀ i, 0 < d i) → (∑ i, d i) = totalDim →
    ∀ (D : ∀ i, DyadicGrid (d i)) (Phi : (Fin n → ℤ) → ℤ), Monotone Phi →
    ∀ (G : Set (∀ i, Box (Fin (d i)))), G ⊆ dyadicPhiRectangles D Phi →
    ∀ E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ),
    (∀ R ∈ G, MeasurableSet (E R)) →
    (∀ R ∈ G, E R ⊆ (flatProductBox R : Set (Fin (∑ i, d i) → ℝ))) →
    Set.Pairwise G (fun R S => Disjoint (E R) (E S)) →
    (∀ R ∈ G, ENNReal.ofReal eta *
      volume (flatProductBox R : Set (Fin (∑ i, d i) → ℝ)) ≤ volume (E R)) →
    volume (shadow G) < ∞ →
    (∀ᵐ x ∂volume, overlap G x < ∞) ∧
      (∫⁻ x in shadow G, ENNReal.ofReal
        (Real.exp (c * (overlap G x).toReal ^ (1 / (n : ℝ))) - 1)) ≤
        ENNReal.ofReal C * volume (shadow G) := by
  intro n totalDim hn eta heta
  obtain ⟨K, hK, hmom⟩ := phi_sparse_overlap_moments n totalDim hn
  let B := K * eta⁻¹
  have hB : 0 < B := mul_pos hK (inv_pos.mpr heta)
  let c := ((Real.exp 2 * B)⁻¹) ^ (1 / (n : ℝ))
  have hc : 0 < c := Real.rpow_pos_of_pos
    (inv_pos.mpr (mul_pos (Real.exp_pos _) hB)) _
  refine ⟨c, Real.exp 4, hc, Real.exp_pos _, ?_⟩
  intro d hd hdim D Phi hPhi G hG E hEm hEs hEd hEv hshadow
  have hgrid : G ⊆ gridRectangles D := by
    intro R hR i
    obtain ⟨a, ha⟩ := hG hR
    exact ⟨_, ha i⟩
  have h := countable_overlap_exponential_of_moments G
    ((countable_gridRectangles D).mono hgrid) hshadow n (by omega) B hB
    (hmom d hd hdim D Phi hPhi G hG eta heta E hEm hEs hEd hEv)
  have hexponent (x : Fin (∑ i, d i) → ℝ) :
      ((overlap G x).toReal / (Real.exp 2 * B)) ^ (1 / (n : ℝ)) =
        c * (overlap G x).toReal ^ (1 / (n : ℝ)) := by
    rw [div_eq_mul_inv, Real.mul_rpow ENNReal.toReal_nonneg
      (inv_nonneg.mpr (mul_pos (Real.exp_pos _) hB).le), mul_comm]
  simpa only [hexponent] using h

end ReyZygmund.Overlap
