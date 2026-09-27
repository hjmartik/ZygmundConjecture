import ReyZygmund.Maximal.SquareLevelSets
import ReyZygmund.Maximal.Signed

/-!
# Grouping the nonzero product differences

The density index is selected from the proved unique last level. Zero
differences are omitted, not assigned a fictitious density level. The upper
part of the grouping has no signed averages outside the corresponding halo.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

noncomputable def nonzeroSquareIndices
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) : Finset (∀ i, Box (Fin (d i))) :=
  (productInterior I N).filter (fun Q => productDifferenceMap Finset.univ Q F ≠ 0)

noncomputable def squareDensityIndex
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (Q : ∀ i, Box (Fin (d i))) : ℤ :=
  if h : Q ∈ nonzeroSquareIndices I N F then
    (existsUnique_square_density_level I N F Q (Finset.mem_filter.mp h).1
      (Finset.mem_filter.mp h).2).exists.choose
  else 0

theorem squareDensityIndex_spec
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (Q : ∀ i, Box (Fin (d i)))
    (hQ : Q ∈ nonzeroSquareIndices I N F) :
    let δ := 1 / (2 : ℝ) ^ ((∑ i, d i) + 1)
    δ * volume.real (productBox Q) <
        volume.real (productBox Q ∩ finiteSquareLevelSet I N F (squareDensityIndex I N F Q)) ∧
      volume.real (productBox Q ∩ finiteSquareLevelSet I N F (squareDensityIndex I N F Q + 1)) ≤
        δ * volume.real (productBox Q) := by
  rw [squareDensityIndex, dite_eq_left hQ]
  exact (existsUnique_square_density_level I N F Q (Finset.mem_filter.mp hQ).1
    (Finset.mem_filter.mp hQ).2).exists.choose_spec

private theorem nonzero_index_descendant
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (Q : ∀ i, Box (Fin (d i)))
    (hQ : Q ∈ nonzeroSquareIndices I N F) : Q ∈ productDescendants I N := by
  apply mem_productDescendants.mpr
  intro i
  exact interior_subset_descendants (I i) (N i)
    (mem_productInterior.mp (Finset.mem_filter.mp hQ).1 i)

theorem productBox_subset_squareDensityHalo
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (Q : ∀ i, Box (Fin (d i)))
    (hQ : Q ∈ nonzeroSquareIndices I N F) :
    productBox Q ⊆ finiteSquareHalo I N F (squareDensityIndex I N F Q) :=
  productBox_subset_finite_root_halo I N _
    (measurableSet_finiteSquareLevelSet I N F _) Q
    (nonzero_index_descendant I N F Q hQ) _ (squareDensityIndex_spec I N F Q hQ).1

/-- Removing the zero applied differences does not change the sum. -/
theorem sum_nonzeroSquareIndices
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) :
    (∑ Q ∈ nonzeroSquareIndices I N F, productDifferenceMap Finset.univ Q F) =
      ∑ Q ∈ productInterior I N, productDifferenceMap Finset.univ Q F := by
  unfold nonzeroSquareIndices
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Q _
  by_cases h : productDifferenceMap Finset.univ Q F = 0 <;> simp [h]

noncomputable def squarePieceIndices
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (n : ℤ) : Finset (∀ i, Box (Fin (d i))) :=
  (nonzeroSquareIndices I N F).filter (fun Q => squareDensityIndex I N F Q = n)

noncomputable def squareLowerIndices
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (n : ℤ) : Finset (∀ i, Box (Fin (d i))) :=
  (nonzeroSquareIndices I N F).filter (fun Q => squareDensityIndex I N F Q < n)

noncomputable def squareUpperIndices
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (n : ℤ) : Finset (∀ i, Box (Fin (d i))) :=
  (nonzeroSquareIndices I N F).filter (fun Q => ¬ squareDensityIndex I N F Q < n)

theorem squareLower_add_squareUpper
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (n : ℤ) :
    (∑ Q ∈ squareLowerIndices I N F n, productDifferenceMap Finset.univ Q F) +
      (∑ Q ∈ squareUpperIndices I N F n, productDifferenceMap Finset.univ Q F) =
      ∑ Q ∈ productInterior I N, productDifferenceMap Finset.univ Q F := by
  rw [← sum_nonzeroSquareIndices I N F]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

/-- Every upper-piece parent lies in the halo at the splitting level. -/
theorem squareUpper_parent_subset_halo
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d) (n : ℤ)
    (Q : ∀ i, Box (Fin (d i))) (hQ : Q ∈ squareUpperIndices I N F n) :
    productBox Q ⊆ finiteSquareHalo I N F n := by
  obtain ⟨hQ0, hlev⟩ := Finset.mem_filter.mp hQ
  exact (productBox_subset_squareDensityHalo I N F Q hQ0).trans
    (finiteSquareHalo_antitone I N F (le_of_not_gt hlev))

theorem squareUpper_signedMaximal_zero_off_halo
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (F : boundedMeasurableFunctions d) (n : ℤ) (x : ProductPoint d)
    (hx : x ∉ finiteSquareHalo I N F n) :
    finiteSignedProductMaximal I N
      (∑ Q ∈ squareUpperIndices I N F n, productDifferenceMap Finset.univ Q F) x = 0 :=
  finiteSignedProductMaximal_sum_eq_zero_off I N hd _
    (fun Q hQ => nonzero_index_descendant I N F Q (Finset.mem_filter.mp hQ).1) F _
    (squareUpper_parent_subset_halo I N F n) x hx

/-- Outside the halo only the lower density pieces can contribute signed averages. -/
theorem signedMaximal_eq_lower_off_halo
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (F : boundedMeasurableFunctions d) (n : ℤ) (x : ProductPoint d)
    (hx : x ∉ finiteSquareHalo I N F n) :
    finiteSignedProductMaximal I N
      (∑ Q ∈ productInterior I N, productDifferenceMap Finset.univ Q F) x =
      finiteSignedProductMaximal I N
        (∑ Q ∈ squareLowerIndices I N F n, productDifferenceMap Finset.univ Q F) x := by
  have hz := squareUpper_signedMaximal_zero_off_halo I N hd F n x hx
  have havg (R : ∀ i, Box (Fin (d i))) (hR : R ∈ productDescendants I N) :
      (productAverageMap Finset.univ R
        (∑ Q ∈ squareUpperIndices I N F n, productDifferenceMap Finset.univ Q F)).1 x = 0 := by
    have hle := Finset.le_sup'
      (fun R => |(productAverageMap Finset.univ R
        (∑ Q ∈ squareUpperIndices I N F n, productDifferenceMap Finset.univ Q F)).1 x|) hR
    change |(productAverageMap Finset.univ R
      (∑ Q ∈ squareUpperIndices I N F n, productDifferenceMap Finset.univ Q F)).1 x| ≤
      finiteSignedProductMaximal I N _ x at hle
    rw [hz] at hle
    exact abs_nonpos_iff.mp hle
  rw [← squareLower_add_squareUpper I N F n]
  unfold finiteSignedProductMaximal
  apply Finset.sup'_congr _ rfl
  intro R hR
  rw [map_add]
  change |(productAverageMap Finset.univ R
      (∑ Q ∈ squareLowerIndices I N F n, productDifferenceMap Finset.univ Q F)).1 x +
    (productAverageMap Finset.univ R
      (∑ Q ∈ squareUpperIndices I N F n, productDifferenceMap Finset.univ Q F)).1 x| = _
  rw [havg R hR, add_zero]

end ReyZygmund
