import ReyZygmund.Geometry.PhiRectangles
import ReyZygmund.Geometry.Grids
import ReyZygmund.Maximal.Euclidean
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Ring

/-! # Extending a dyadic side-length relation

Extend the integer side-exponent function using floors of base-two logarithms. The
extension agrees at integer powers of two, so the dyadic family is contained in
the family with arbitrary side lengths. Grid generations are the negatives of
side-length exponents.

-/

open BoxIntegral
open scoped BigOperators Classical

namespace ReyZygmund.Continuous

open Geometry

variable {n : ℕ}

/-- The paper's positive extension of an integer side-exponent function. -/
noncomputable def dyadicPhiExtension (Phi : (Fin n → ℤ) → ℤ)
    (s : Fin n → Set.Ioi (0 : ℝ)) : Set.Ioi (0 : ℝ) :=
  ⟨(2 : ℝ) ^ Phi (fun j => ⌊Real.logb 2 (s j).1⌋),
    zpow_pos (by norm_num : (0 : ℝ) < 2) _⟩

theorem dyadicPhiExtension_mono (Phi : (Fin n → ℤ) → ℤ) (hPhi : Monotone Phi) :
    Monotone (dyadicPhiExtension Phi) := by
  intro s t hst
  change (2 : ℝ) ^ Phi (fun j => ⌊Real.logb 2 (s j).1⌋) ≤
    (2 : ℝ) ^ Phi (fun j => ⌊Real.logb 2 (t j).1⌋)
  apply zpow_le_zpow_right₀ (by norm_num)
  apply hPhi
  intro j
  exact Int.floor_mono (Real.logb_le_logb_of_le (by norm_num) (s j).2 (hst j))

/-- Exact recovery holds for every integer exponent, not just nonnegative ones. -/
theorem dyadicPhiExtension_zpow (Phi : (Fin n → ℤ) → ℤ) (k : Fin n → ℤ) :
    (dyadicPhiExtension Phi
      (fun j => ⟨(2 : ℝ) ^ k j, zpow_pos (by norm_num : (0 : ℝ) < 2) _⟩)).1 =
        (2 : ℝ) ^ Phi k := by
  change (2 : ℝ) ^ Phi (fun j => ⌊Real.logb 2 ((2 : ℝ) ^ k j)⌋) = _
  apply congrArg (fun t : Fin n → ℤ => (2 : ℝ) ^ Phi t)
  funext j
  rw [← Real.rpow_intCast, Real.logb_rpow (by norm_num) (by norm_num), Int.floor_intCast]

/-- Grid rectangles with the paper's prescribed integer side exponents.
The generation of a cube of side `2 ^ k` is `-k`. -/
def dyadicPhiRectangles {d : Fin (n + 1) → ℕ}
    (D : ∀ i, DyadicGrid (d i)) (Phi : (Fin n → ℤ) → ℤ) :
    Set (∀ i, Box (Fin (d i))) :=
  {R | ∃ k : Fin n → ℤ,
    ∀ i, R i ∈ (D i).cubes (-((Fin.snoc k (Phi k) : Fin (n + 1) → ℤ) i))}

/-- No monotonicity or positive-dimension premise is needed for the
inclusion; monotonicity is needed when applying the continuous endpoint. -/
theorem dyadicPhiRectangles_subset_continuous {d : Fin (n + 1) → ℕ}
    (D : ∀ i, DyadicGrid (d i)) (Phi : (Fin n → ℤ) → ℤ) :
    dyadicPhiRectangles D Phi ⊆ continuousPhiRectangles d (dyadicPhiExtension Phi) := by
  rintro R ⟨k, hk⟩
  let s : Fin n → Set.Ioi (0 : ℝ) :=
    fun j => ⟨(2 : ℝ) ^ k j, zpow_pos (by norm_num : (0 : ℝ) < 2) _⟩
  have hs : (dyadicPhiExtension Phi s).1 = (2 : ℝ) ^ Phi k :=
    dyadicPhiExtension_zpow Phi k
  have hside (i : Fin (n + 1)) :
      (2 : ℝ) ^ ((Fin.snoc k (Phi k) : Fin (n + 1) → ℤ) i) =
        (Fin.snoc (fun j => (s j).1) (dyadicPhiExtension Phi s).1 :
          Fin (n + 1) → ℝ) i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, hs]
    · simp only [Fin.snoc_castSucc]
      rfl
  refine ⟨s, ?_⟩
  intro i a
  have hwidth := (D i).width
    (-((Fin.snoc k (Phi k) : Fin (n + 1) → ℤ) i)) (R i) (hk i) a
  simp only [neg_neg] at hwidth
  exact hwidth.trans (hside i)

/-- Family inclusion gives domination of supported averages. The algebraic identity
permits arbitrary input; applications to averages require local integrability. -/
theorem dyadic_maximal_le_continuous {d : Fin (n + 1) → ℕ}
    (D : ∀ i, DyadicGrid (d i)) (Phi : (Fin n → ℤ) → ℤ)
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (x : Fin (∑ i, d i) → ℝ) :
    euclideanFamilyMaximal (dyadicPhiRectangles D Phi) f x ≤
      euclideanFamilyMaximal (continuousPhiRectangles d (dyadicPhiExtension Phi)) f x := by
  unfold euclideanFamilyMaximal
  apply iSup_le
  intro R
  exact le_iSup_of_le
    (⟨R.1, dyadicPhiRectangles_subset_continuous D Phi R.2⟩ :
      continuousPhiRectangles d (dyadicPhiExtension Phi)) le_rfl

end ReyZygmund.Continuous
