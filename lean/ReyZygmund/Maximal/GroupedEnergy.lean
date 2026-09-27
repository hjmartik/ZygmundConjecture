import ReyZygmund.Maximal.SquareGrouping
import ReyZygmund.Geometry.ProductL2
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! # Regrouping energy by the density index

Product orthogonality regroups the square integral of a finite difference sum over
its integer density indices. The final comparison uses the summable strict integer
tail.

-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

private theorem lower_subset_productInterior
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (n : ℤ) :
    squareLowerIndices I N F n ⊆ productInterior I N := by
  intro Q hQ
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hQ).1).1

private theorem piece_subset_productInterior
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (j : ℤ) :
    squarePieceIndices I N F j ⊆ productInterior I N := by
  intro Q hQ
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hQ).1).1

private theorem density_image_lt
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (n j : ℤ)
    (hj : j ∈ (squareLowerIndices I N F n).image (squareDensityIndex I N F)) : j < n := by
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hj
  exact (Finset.mem_filter.mp hQ).2

private theorem lower_density_fiber
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (n j : ℤ) (hjn : j < n) :
    (squareLowerIndices I N F n).filter (fun Q => squareDensityIndex I N F Q = j) =
      squarePieceIndices I N F j := by
  ext Q
  simp only [squareLowerIndices, squarePieceIndices, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hQ, _⟩, heq⟩
    exact ⟨hQ, heq⟩
  · rintro ⟨hQ, heq⟩
    refine ⟨⟨hQ, ?_⟩, heq⟩
    rw [heq]
    exact hjn

/-- Exact energy regrouping over the finite image of the lower density
indices. The orthogonality is derived for the product differences. -/
theorem squareLower_energy_eq_sum
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (F : boundedMeasurableFunctions d) (n : ℤ) :
    (∫ x in productBox I, (∑ Q ∈ squareLowerIndices I N F n,
      (productDifferenceMap Finset.univ Q F).1 x) ^ 2) =
      ∑ j ∈ (squareLowerIndices I N F n).image (squareDensityIndex I N F),
        ∫ x in productBox I, (∑ Q ∈ squarePieceIndices I N F j,
          (productDifferenceMap Finset.univ Q F).1 x) ^ 2 := by
  rw [productDifference_integral_sum_sq I N hd F (squareLowerIndices I N F n)
    (lower_subset_productInterior I N F n)]
  have hreindex :
      (∑ j ∈ (squareLowerIndices I N F n).image (squareDensityIndex I N F),
        ∑ Q ∈ (squareLowerIndices I N F n).filter (fun Q => squareDensityIndex I N F Q = j),
          ∫ x in productBox I, ((productDifferenceMap Finset.univ Q F).1 x) ^ 2) =
        ∑ Q ∈ squareLowerIndices I N F n,
          ∫ x in productBox I, ((productDifferenceMap Finset.univ Q F).1 x) ^ 2 :=
    Finset.sum_fiberwise_of_maps_to
      (fun Q hQ => Finset.mem_image.mpr ⟨Q, hQ, rfl⟩) _
  rw [← hreindex]
  apply Finset.sum_congr rfl
  intro j hj
  rw [lower_density_fiber I N F n j (density_image_lt I N F n j hj)]
  exact (productDifference_integral_sum_sq I N hd F (squarePieceIndices I N F j)
    (piece_subset_productInterior I N F j)).symm

/-- Per-piece energy bounds control the lower sum by a convergent
strict level tail. No summability outside `j < n` is required. -/
theorem squareLower_energy_le_tsum
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (F : boundedMeasurableFunctions d) (n : ℤ)
    (B : ℝ) (hB : 0 ≤ B) (b : ℤ → ℝ) (hb0 : ∀ j, 0 ≤ b j)
    (htail : Summable (fun j : ℤ => if j < n then b j else 0))
    (hpiece : ∀ j < n,
      (∫ x in productBox I, (∑ Q ∈ squarePieceIndices I N F j,
        (productDifferenceMap Finset.univ Q F).1 x) ^ 2) ≤ B * b j) :
    (∫ x in productBox I, (∑ Q ∈ squareLowerIndices I N F n,
      (productDifferenceMap Finset.univ Q F).1 x) ^ 2) ≤
      B * (∑' j : ℤ, if j < n then b j else 0) := by
  have hfinite : (∑ j ∈ (squareLowerIndices I N F n).image (squareDensityIndex I N F), b j) ≤
      ∑' j : ℤ, if j < n then b j else 0 := by
    calc
      _ = ∑ j ∈ (squareLowerIndices I N F n).image (squareDensityIndex I N F),
          (if j < n then b j else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [ite_eq_left (density_image_lt I N F n j hj)]
      _ ≤ _ := Summable.sum_le_tsum _ (fun j _ => by
        by_cases hj : j < n
        · rw [ite_eq_left hj]
          exact hb0 j
        · rw [ite_eq_right hj]) htail
  rw [squareLower_energy_eq_sum I N hd F n]
  calc
    _ ≤ ∑ j ∈ (squareLowerIndices I N F n).image (squareDensityIndex I N F), B * b j := by
      apply Finset.sum_le_sum
      intro j hj
      exact hpiece j (density_image_lt I N F n j hj)
    _ = B * (∑ j ∈ (squareLowerIndices I N F n).image (squareDensityIndex I N F), b j) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hfinite hB

end ReyZygmund
