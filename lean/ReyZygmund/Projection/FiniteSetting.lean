import ReyZygmund.MathlibOnly.Projections
import ReyZygmund.Geometry.ProductFiniteSetting
import ReyZygmund.Geometry.PartialOperatorMaps
import ReyZygmund.Projection.CommonProjection
import ReyZygmund.Projection.AveragingRectangles

/-! # Finite families and the projection

The prescribed bottom scale determines the number of subdivisions in each
coordinate. The public cube and rectangle sets are therefore finite, and the
projection's sum agrees with the finite linear operator on bounded measurable
functions.
-/

noncomputable section

open BoxIntegral
open scoped BigOperators Classical

namespace ReyZygmund.Geometry

open MathlibOnly (CubeGrid finiteCubes)

/-- All cubes at or above the cutoff are exactly the finite descendants. -/
theorem finiteCubes_eq_descendants {d : ℕ} (D : CubeGrid d) (hd : 0 < d)
    {I : Box (Fin d)} {l k : ℤ} (hI : I ∈ D.cubes l) (hcut : -k ≤ l) :
    finiteCubes D I k = (descendants I (l + k).toNat : Set (Box (Fin d))) := by
  have htop : I ∈ D.cubesAtGeneration (-l) := by
    simpa only [MathlibOnly.CubeGrid.cubesAtGeneration, neg_neg] using hI
  have hdepth : ((l + k).toNat : ℤ) = l + k := by omega
  ext Q
  change ((∃ a : ℤ, -k ≤ a ∧ Q ∈ D.cubes a) ∧
    (Q : Set (Fin d → ℝ)) ⊆ I) ↔ Q ∈ descendants I _
  constructor
  · rintro ⟨⟨a, hka, hQa⟩, hQI⟩
    have hal := D.sideExponent_le_of_le hd hQa hI hQI
    have hindex : -l + ((l - a).toNat : ℤ) = -a := by omega
    refine mem_descendants.mpr ⟨(l - a).toNat, by omega, ?_⟩
    apply (D.mem_level_iff htop).mpr
    refine ⟨?_, hQI⟩
    simpa only [hindex, MathlibOnly.CubeGrid.cubesAtGeneration, neg_neg] using hQa
  · intro hQ
    obtain ⟨r, hr, hQr⟩ := mem_descendants.mp hQ
    have hgen := D.mem_cubes_of_mem_level htop hQr
    refine ⟨⟨l - (r : ℤ), by omega, ?_⟩, (level I r).le_of_mem hQr⟩
    simpa only [MathlibOnly.CubeGrid.cubesAtGeneration, neg_add_rev, neg_neg,
      sub_eq_add_neg, add_comm] using hgen

/-- The full average is the product of all coordinate average maps. -/
theorem fullAverage_eq_productAverageMap {m : ℕ} {d : Fin m → ℕ}
    (R : MathlibOnly.Rectangle d) (f : boundedMeasurableFunctions d) :
    MathlibOnly.fullAverage R f.1 = (productAverageMap Finset.univ R f).1 :=
  partialAverage_eq_productAverageMap Finset.univ R f

end ReyZygmund.Geometry

namespace ReyZygmund.Projection

open Geometry
open MathlibOnly (CubeGrid Rectangle finiteRectangles removedRectangles)

variable {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, CubeGrid (d i)) (hd : ∀ i, 0 < d i)
    {I : Rectangle d} {l : Fin m → ℤ} {k : ℤ}
    (hI : ∀ i, I i ∈ (D i).cubes (l i)) (hcut : ∀ i, -k ≤ l i)

include hd hI hcut

/-- The finite product grid has the same indices as the product of descendants. -/
theorem finiteRectangles_eq_productDescendants :
    finiteRectangles D I k =
      (productDescendants I (fun i => (l i + k).toNat) : Set (Rectangle d)) := by
  ext R
  simp only [finiteRectangles, Set.mem_ofPred_eq, Finset.mem_coe, mem_productDescendants]
  apply forall_congr'
  intro i
  rw [finiteCubes_eq_descendants (D i) (hd i) (hI i) (hcut i)]
  rfl

/-- A family contained in the finite product grid is finite. -/
theorem finite_of_subset_finiteRectangles {G : Set (Rectangle d)}
    (hG : G ⊆ finiteRectangles D I k) : G.Finite := by
  rw [finiteRectangles_eq_productDescendants D hd hI hcut] at hG
  exact (productDescendants I (fun i => (l i + k).toNat)).finite_toSet.subset hG

/-- Removed rectangles are counted once by the finite difference-index set. -/
theorem removedRectangles_eq_removedIndices (G : Finset (Rectangle d)) :
    removedRectangles D I k (G : Set (Rectangle d)) =
      (removedIndices I (fun i => (l i + k).toNat) G : Set (Rectangle d)) := by
  ext L
  simp only [removedRectangles, Set.mem_ofPred_eq, Finset.mem_coe, removedIndices,
    Finset.mem_filter, mem_productInterior]
  apply and_congr ?_ Iff.rfl
  apply forall_congr'
  intro i
  rw [interiorCubes_eq_interior (D i) (hd i) (hI i) (hcut i)]
  rfl

/-- The public projection is the finite removed-difference operator.
Its real-valued sum has a finite index set. -/
theorem projection_eq_finiteProjectionMap (G : Finset (Rectangle d))
    (f : boundedMeasurableFunctions d) :
    MathlibOnly.projection D I k (G : Set (Rectangle d)) f.1 =
      (finiteProjectionMap I (fun i => (l i + k).toNat) G f).1 := by
  rw [finiteProjectionMap_apply]
  funext x
  simp only [MathlibOnly.projection, Pi.sub_apply, Finset.sum_apply]
  congr 1
  rw [removedRectangles_eq_removedIndices D hd hI hcut]
  calc
    _ = ∑ L ∈ removedIndices I (fun i => (l i + k).toNat) G,
        MathlibOnly.fullDifference L f.1 x :=
      Finset.tsum_subtype' (removedIndices I (fun i => (l i + k).toNat) G)
        (fun L => MathlibOnly.fullDifference L f.1 x)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro L _
      exact congrFun (fullDifference_eq_productDifferenceMap L f) x

end ReyZygmund.Projection
