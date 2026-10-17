import ReyZygmund.Projection.FiniteSetting
import ReyZygmund.Projection.CrossFiniteSetting

/-! # Averaging rectangles in the finite grid

The public family consists of the finite product descendants with a maximal
cross-partition cube in at least one coordinate. Completing the other factors
with the top cube does not change which projections are eligible.
-/

noncomputable section

open BoxIntegral
open scoped BigOperators Classical

namespace ReyZygmund.Projection

open Geometry
open MathlibOnly (CubeGrid Rectangle)

variable {m : ℕ} {d : Fin m → ℕ}

/-- The public averaging rectangles are precisely the finite averaging family. -/
theorem averagingRectangles_eq_finiteAveragingRectangles
    (D : ∀ i, CubeGrid (d i)) (hd : ∀ i, 0 < d i)
    {I : Rectangle d} {l : Fin m → ℤ} {k : ℤ}
    (hI : ∀ i, I i ∈ (D i).cubes (l i)) (hcut : ∀ i, -k ≤ l i)
    (G : Finset (Rectangle d)) :
    MathlibOnly.averagingRectangles D I k (G : Set (Rectangle d)) =
      (averagingRectangles I (fun i => (l i + k).toNat) G : Set (Rectangle d)) := by
  ext R
  simp only [MathlibOnly.averagingRectangles, Set.mem_ofPred_eq,
    finiteRectangles_eq_productDescendants D hd hI hcut,
    Finset.mem_coe, averagingRectangles, Finset.mem_filter]
  apply and_congr_right
  intro _
  apply exists_congr
  intro j
  rw [crossPartition_eq_partitionCubes D hI hcut G j]
  have hcomplete :
      completePartialRectangle I (Finset.univ.erase j) (fun i => R i) =
        Function.update R j (I j) := by
    funext i
    by_cases hij : i = j
    · subst i
      simp [completePartialRectangle]
    · simp [completePartialRectangle, hij]
  rw [hcomplete, eligibleProjections_update]
  rfl

end ReyZygmund.Projection
