import ReyZygmund.Geometry.Grids
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Alternating shifted dyadic grids of half-open cubes

The shift index has entries in `Fin 3`, representing the numerators of
`0, 1/3, 2/3`. At generation `n` the side is `2 ^ (-n)` and the phase is
`(-1) ^ n`. All grid fields are proved for the `(lower, upper]`
boxes, including dimension zero. Prescribed covering is a separate result.
-/

noncomputable section

open BoxIntegral
open scoped Classical

namespace ReyZygmund.Geometry

variable {d : ℕ}

/-- The alternating shifted cube at generation `n`. -/
def shiftedDyadicCube (a : Fin d → Fin 3) (n : ℤ)
    (z : Fin d → ℤ) : Box (Fin d) :=
  rootBox
    (fun i => (2 : ℝ) ^ (-n) *
      ((z i : ℝ) + (-1 : ℝ) ^ n * ((a i).val : ℝ) / 3)) (-n)

/-- Ceiling selects the owning shifted cube, including at its upper boundary. -/
theorem mem_shiftedDyadicCube_iff (a : Fin d → Fin 3) (n : ℤ)
    (z : Fin d → ℤ) (x : Fin d → ℝ) :
    x ∈ shiftedDyadicCube a n z ↔
      ∀ i, ⌈x i / (2 : ℝ) ^ (-n) - (-1 : ℝ) ^ n * ((a i).val : ℝ) / 3⌉ =
        z i + 1 := by
  change (∀ i, (2 : ℝ) ^ (-n) *
      ((z i : ℝ) + (-1 : ℝ) ^ n * ((a i).val : ℝ) / 3) < x i ∧
    x i ≤ (2 : ℝ) ^ (-n) *
      ((z i : ℝ) + (-1 : ℝ) ^ n * ((a i).val : ℝ) / 3) + (2 : ℝ) ^ (-n)) ↔ _
  have hL : 0 < (2 : ℝ) ^ (-n) := zpow_pos (by norm_num) _
  simp only [Int.ceil_eq_iff, Int.cast_add, Int.cast_one, add_sub_cancel_right]
  apply forall_congr'
  intro i
  constructor
  · rintro ⟨hl, hu⟩
    constructor
    · exact lt_sub_iff_add_lt.mpr ((lt_div_iff₀' hL).mpr hl)
    · apply sub_le_iff_le_add.mpr
      apply (div_le_iff₀' hL).mpr
      calc
        x i ≤ (2 : ℝ) ^ (-n) *
            ((z i : ℝ) + (-1 : ℝ) ^ n * ((a i).val : ℝ) / 3) +
              (2 : ℝ) ^ (-n) := hu
        _ = (2 : ℝ) ^ (-n) *
            ((z i : ℝ) + 1 + (-1 : ℝ) ^ n * ((a i).val : ℝ) / 3) := by ring
  · rintro ⟨hl, hu⟩
    constructor
    · exact (lt_div_iff₀' hL).mp (lt_sub_iff_add_lt.mp hl)
    · have hh := (div_le_iff₀' hL).mp (sub_le_iff_le_add.mp hu)
      calc
        x i ≤ (2 : ℝ) ^ (-n) *
            ((z i : ℝ) + 1 + (-1 : ℝ) ^ n * ((a i).val : ℝ) / 3) := hh
        _ = (2 : ℝ) ^ (-n) *
            ((z i : ℝ) + (-1 : ℝ) ^ n * ((a i).val : ℝ) / 3) +
              (2 : ℝ) ^ (-n) := by ring

/-- Integer indices describe distinct boxes in every dimension. -/
theorem shiftedDyadicCube_injective (a : Fin d → Fin 3) (n : ℤ) :
    Function.Injective (shiftedDyadicCube a n) := by
  intro z w h
  funext i
  have hi := congrArg (fun Q : Box (Fin d) => Q.lower i) h
  change (2 : ℝ) ^ (-n) *
      ((z i : ℝ) + (-1 : ℝ) ^ n * ((a i).val : ℝ) / 3) =
    (2 : ℝ) ^ (-n) *
      ((w i : ℝ) + (-1 : ℝ) ^ n * ((a i).val : ℝ) / 3) at hi
  exact Int.cast_injective (add_right_cancel
    (mul_left_cancel₀ (ne_of_gt (zpow_pos (by norm_num : (0 : ℝ) < 2) (-n))) hi))

private theorem shiftedDyadicCube_disjoint (a : Fin d → Fin 3) (n : ℤ)
    {z w : Fin d → ℤ} (hzw : z ≠ w) :
    Disjoint (shiftedDyadicCube a n z : Set (Fin d → ℝ)) (shiftedDyadicCube a n w) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hzw
  funext i
  exact add_right_cancel
    (((mem_shiftedDyadicCube_iff a n z x).mp hx i).symm.trans
      ((mem_shiftedDyadicCube_iff a n w x).mp hy i))

/-- The phase reversal contributes the integral shift needed by each
dyadic child. The formula includes negative integer generations. -/
theorem shiftedDyadicCube_splitCenterBox (a : Fin d → Fin 3) (n : ℤ)
    (z : Fin d → ℤ) (s : Set (Fin d)) :
    (shiftedDyadicCube a n z).splitCenterBox s =
      shiftedDyadicCube a (n + 1) (fun i =>
        2 * z i + (if Even n then 1 else -1) * ((a i).val : ℤ) +
          (if i ∈ s then 1 else 0)) := by
  have hscale : (2 : ℝ) ^ (-(n + 1)) = (2 : ℝ) ^ (-n) / 2 := by
    rw [show -(n + 1) = -n - 1 by ring, zpow_sub₀ (by norm_num), zpow_one]
  have hphase : (-1 : ℝ) ^ (n + 1) = -(-1 : ℝ) ^ n := by
    rw [zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0), mul_neg, mul_one]
  have hsign : ((if Even n then 1 else -1 : ℤ) : ℝ) = (-1 : ℝ) ^ n := by
    by_cases hn : Even n <;> simp [neg_one_zpow_eq_ite, hn]
  have hcorners (i : Fin d) :
      ((shiftedDyadicCube a n z).splitCenterBox s).lower i =
        (shiftedDyadicCube a (n + 1) (fun j =>
          2 * z j + (if Even n then 1 else -1) * ((a j).val : ℤ) +
            (if j ∈ s then 1 else 0))).lower i ∧
      ((shiftedDyadicCube a n z).splitCenterBox s).upper i =
        (shiftedDyadicCube a (n + 1) (fun j =>
          2 * z j + (if Even n then 1 else -1) * ((a j).val : ℤ) +
            (if j ∈ s then 1 else 0))).upper i := by
    simp only [shiftedDyadicCube, rootBox, Box.splitCenterBox, Set.piecewise, hscale, hphase]
    by_cases hi : i ∈ s
    · simp only [ite_eq_left hi, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one,
        Int.cast_natCast, hsign]
      constructor <;> ring
    · simp only [ite_eq_right hi, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_zero,
        Int.cast_natCast, hsign]
      constructor <;> ring
  apply Box.ext
  intro x
  simp only [Box.mem_def]
  apply forall_congr'
  intro i
  rw [(hcorners i).1, (hcorners i).2]

/-- The alternating shifted dyadic grid. Its cubes partition Euclidean space
at each integer generation, with dyadic children at the next generation. -/
def shiftedDyadicGrid (d : ℕ) (a : Fin d → Fin 3) : DyadicGrid d where
  cubes n := Set.range (shiftedDyadicCube a n)
  width n Q hQ i := by
    obtain ⟨z, rfl⟩ := hQ
    exact rootBox_width _ _ i
  disjoint n := by
    rintro _ ⟨z, rfl⟩ _ ⟨w, rfl⟩ hne
    exact shiftedDyadicCube_disjoint a n
      (fun h => hne (congrArg (shiftedDyadicCube a n) h))
  cover n x := by
    let z : Fin d → ℤ := fun i =>
      ⌈x i / (2 : ℝ) ^ (-n) - (-1 : ℝ) ^ n * ((a i).val : ℝ) / 3⌉ - 1
    refine ⟨shiftedDyadicCube a n z, ⟨z, rfl⟩, ?_⟩
    apply (mem_shiftedDyadicCube_iff a n z x).mpr
    intro i
    exact (sub_add_cancel _ _).symm
  children n Q hQ R hR := by
    obtain ⟨z, rfl⟩ := hQ
    obtain ⟨s, rfl⟩ := Prepartition.mem_splitCenter.mp hR
    exact ⟨_, (shiftedDyadicCube_splitCenterBox a n z s).symm⟩

end ReyZygmund.Geometry
