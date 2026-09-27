import ReyZygmund.Geometry.Grids
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The standard dyadic grid of half-open cubes

At generation `n`, the cube indexed by `k : Fin d → ℤ` has side `2 ^ (-n)`
and lower corner `2 ^ (-n) * k`. The `(lower, upper]` convention assigns a
point to the index `ceil (x / side) - 1`, including at integer boundaries.
All geometric fields are proved; no countability or analytic estimate is assumed.
-/

noncomputable section

open BoxIntegral
open scoped Classical

namespace ReyZygmund.Geometry

variable {d : ℕ}

/-- The origin-aligned cube with integer index `k` at generation `n`. -/
def standardDyadicCube (n : ℤ) (k : Fin d → ℤ) : Box (Fin d) :=
  rootBox (fun i => (2 : ℝ) ^ (-n) * (k i : ℝ)) (-n)

/-- Ceiling, not floor, gives the owning cube for the `(lower, upper]`
boundary convention. -/
theorem mem_standardDyadicCube_iff (n : ℤ) (k : Fin d → ℤ) (x : Fin d → ℝ) :
    x ∈ standardDyadicCube n k ↔
      ∀ i, ⌈x i / (2 : ℝ) ^ (-n)⌉ = k i + 1 := by
  change (∀ i, (2 : ℝ) ^ (-n) * (k i : ℝ) < x i ∧
    x i ≤ (2 : ℝ) ^ (-n) * (k i : ℝ) + (2 : ℝ) ^ (-n)) ↔ _
  have hs : 0 < (2 : ℝ) ^ (-n) := zpow_pos (by norm_num) _
  simp only [Int.ceil_eq_iff, Int.cast_add, Int.cast_one, add_sub_cancel_right,
    lt_div_iff₀' hs, div_le_iff₀' hs, mul_add, mul_one]

/-- Distinct integer indices produce distinct boxes, also when the
coordinate type is empty. -/
theorem standardDyadicCube_injective (n : ℤ) :
    Function.Injective (standardDyadicCube (d := d) n) := by
  intro k l h
  funext i
  have hi := congrArg (fun Q : Box (Fin d) => Q.lower i) h
  change (2 : ℝ) ^ (-n) * (k i : ℝ) = (2 : ℝ) ^ (-n) * (l i : ℝ) at hi
  exact Int.cast_injective
    (mul_left_cancel₀ (ne_of_gt (zpow_pos (by norm_num : (0 : ℝ) < 2) (-n))) hi)

private theorem standardDyadicCube_disjoint (n : ℤ) {k l : Fin d → ℤ}
    (hkl : k ≠ l) :
    Disjoint (standardDyadicCube n k : Set (Fin d → ℝ)) (standardDyadicCube n l) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hkl
  funext i
  exact add_right_cancel
    (((mem_standardDyadicCube_iff n k x).mp hx i).symm.trans
      ((mem_standardDyadicCube_iff n l x).mp hy i))

/-- Each dyadic child has the even/odd integer index prescribed by
its lower/upper coordinate choices. -/
theorem standardDyadicCube_splitCenterBox (n : ℤ) (k : Fin d → ℤ)
    (s : Set (Fin d)) :
    (standardDyadicCube n k).splitCenterBox s =
      standardDyadicCube (n + 1) (fun i => 2 * k i + (if i ∈ s then 1 else 0)) := by
  have hscale : (2 : ℝ) ^ (-(n + 1)) = (2 : ℝ) ^ (-n) / 2 := by
    rw [show -(n + 1) = -n - 1 by ring, zpow_sub₀ (by norm_num), zpow_one]
  have hcorners (i : Fin d) :
      ((standardDyadicCube n k).splitCenterBox s).lower i =
        (standardDyadicCube (n + 1)
          (fun j => 2 * k j + (if j ∈ s then 1 else 0))).lower i ∧
      ((standardDyadicCube n k).splitCenterBox s).upper i =
        (standardDyadicCube (n + 1)
          (fun j => 2 * k j + (if j ∈ s then 1 else 0))).upper i := by
    simp only [standardDyadicCube, rootBox, Box.splitCenterBox, Set.piecewise, hscale]
    by_cases hi : i ∈ s
    · simp only [ite_eq_left hi, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one]
      constructor <;> ring
    · simp only [ite_eq_right hi, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_zero]
      constructor <;> ring
  apply Box.ext
  intro x
  simp only [Box.mem_def]
  apply forall_congr'
  intro i
  rw [(hcorners i).1, (hcorners i).2]

/-- The concrete standard dyadic grid. Its levels partition all of `ℝ^d`,
and its dyadic children belong to the next generation. -/
def standardDyadicGrid (d : ℕ) : DyadicGrid d where
  cubes n := Set.range (standardDyadicCube (d := d) n)
  width n Q hQ i := by
    obtain ⟨k, rfl⟩ := hQ
    exact rootBox_width _ _ i
  disjoint n := by
    rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩ hne
    exact standardDyadicCube_disjoint n
      (fun h => hne (congrArg (standardDyadicCube n) h))
  cover n x := by
    let k : Fin d → ℤ := fun i => ⌈x i / (2 : ℝ) ^ (-n)⌉ - 1
    refine ⟨standardDyadicCube n k, ⟨k, rfl⟩, ?_⟩
    apply (mem_standardDyadicCube_iff n k x).mpr
    intro i
    exact (sub_add_cancel _ _).symm
  children n Q hQ R hR := by
    obtain ⟨k, rfl⟩ := hQ
    obtain ⟨s, rfl⟩ := Prepartition.mem_splitCenter.mp hR
    exact ⟨_, (standardDyadicCube_splitCenterBox n k s).symm⟩

end ReyZygmund.Geometry
