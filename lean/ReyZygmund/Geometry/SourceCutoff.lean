import ReyZygmund.Geometry.GridFamilies
import ReyZygmund.Geometry.ProductContainment
import ReyZygmund.Geometry.ProductFiniteSetting

/-! # A common smallest side length

For a top cube at generation `n i`, the smallest side `2^(-k)` corresponds to
dyadic depth `(k - n i).toNat`. The set and constancy identities are pointwise,
on arbitrary supplied dyadic grids.

-/

open BoxIntegral
open scoped Classical

open ReyZygmund.MathlibOnly (CubeGrid gridRectangles)

namespace ReyZygmund.Geometry

open Projection

private theorem source_mem_descendants_width_iff {e : ℕ} (he : 0 < e)
    (D : CubeGrid e) (n k : ℤ) (I Q : Box (Fin e))
    (hI : I ∈ D.cubesAtGeneration n) (hnk : n ≤ k) :
    Q ∈ descendants I (k - n).toNat ↔
      (∃ a, Q ∈ D.cubesAtGeneration a) ∧ Q ≤ I ∧
        ∀ u, (2 : ℝ) ^ (-k) ≤ Q.upper u - Q.lower u := by
  have hcut : n + ((k - n).toNat : ℤ) = k := by omega
  constructor
  · intro hQ
    obtain ⟨r, hr, hQr⟩ := mem_descendants.mp hQ
    have hgen := D.mem_cubes_of_mem_level hI hQr
    refine ⟨⟨n + (r : ℤ), hgen⟩, (level I r).le_of_mem hQr, ?_⟩
    intro u
    rw [D.width _ Q hgen u]
    apply (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr
    omega
  · rintro ⟨⟨a, hQa⟩, hQI, hw⟩
    have hna : n ≤ a := by
      have h := D.sideExponent_le_of_le he hQa hI hQI
      omega
    have hwidth := hw ⟨0, he⟩
    rw [D.width a Q hQa] at hwidth
    have hak := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hwidth
    have hindex : n + ((a - n).toNat : ℤ) = a := by omega
    refine mem_descendants.mpr ⟨(a - n).toNat, by omega, ?_⟩
    exact (D.mem_level_iff hI).mpr ⟨by simpa only [hindex] using hQa, hQI⟩

private theorem source_mem_interior_width_iff {e : ℕ} (he : 0 < e)
    (D : CubeGrid e) (n k : ℤ) (I Q : Box (Fin e))
    (hI : I ∈ D.cubesAtGeneration n) (hnk : n ≤ k) :
    Q ∈ interior I (k - n).toNat ↔
      (∃ a, Q ∈ D.cubesAtGeneration a) ∧ Q ≤ I ∧
        ∀ u, (2 : ℝ) ^ (-k) < Q.upper u - Q.lower u := by
  have hset : MathlibOnly.interiorCubes D I k =
      (interior I (k - n).toNat : Set (Box (Fin e))) := by
    simpa only [sub_eq_add_neg, add_comm] using
      interiorCubes_eq_interior D (k := k) he (show I ∈ D.cubes (-n) from hI) (by omega)
  change Q ∈ (interior I (k - n).toNat : Set (Box (Fin e))) ↔ _
  rw [← hset]
  constructor
  · rintro ⟨⟨a, hka, hQa⟩, hQI⟩
    refine ⟨⟨-a, ?_⟩, hQI, ?_⟩
    · simpa only [CubeGrid.cubesAtGeneration, neg_neg] using hQa
    · intro u
      rw [D.side_length a Q hQa u]
      exact (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr hka
  · rintro ⟨⟨a, hQa⟩, hQI, hw⟩
    have hwidth := hw ⟨0, he⟩
    rw [D.width a Q hQa] at hwidth
    exact ⟨⟨-a,
      (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hwidth, hQa⟩, hQI⟩

private theorem source_mem_leaves_width_iff {e : ℕ} (he : 0 < e)
    (D : CubeGrid e) (n k : ℤ) (I Q : Box (Fin e))
    (hI : I ∈ D.cubesAtGeneration n) (hnk : n ≤ k) :
    Q ∈ leaves I (k - n).toNat ↔
      (∃ a, Q ∈ D.cubesAtGeneration a) ∧ Q ≤ I ∧
        ∀ u, Q.upper u - Q.lower u = (2 : ℝ) ^ (-k) := by
  rw [common_cutoff_leaves_iff D n k I Q hI hnk]
  constructor
  · rintro ⟨hQ, hQI⟩
    exact ⟨⟨k, hQ⟩, hQI, D.width k Q hQ⟩
  · rintro ⟨⟨a, hQa⟩, hQI, hw⟩
    have hwidth := hw ⟨0, he⟩
    rw [D.width a Q hQa] at hwidth
    have hneg := (zpow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).injective hwidth
    have hak : a = k := by omega
    exact ⟨hak ▸ hQa, hQI⟩

variable {m : ℕ} {d : Fin m → ℕ}

/-- The paper's full finite family, including cubes of the cutoff side. -/
theorem source_productDescendants_iff
    (hd : ∀ i, 0 < d i) (D : ∀ i, CubeGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubesAtGeneration (n i))
    (hnk : ∀ i, n i ≤ k) (R : ∀ i, Box (Fin (d i))) :
    R ∈ productDescendants I (fun i => (k - n i).toNat) ↔
      R ∈ gridRectangles D ∧ productRectangle R ⊆ productRectangle I ∧
        ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u := by
  rw [mem_gridRectangles_iff]
  constructor
  · intro hR
    have hc (i : Fin m) := (source_mem_descendants_width_iff (hd i) (D i)
      (n i) k (I i) (R i) (hI i) (hnk i)).mp (mem_productDescendants.mp hR i)
    exact ⟨fun i => (hc i).1, (productRectangle_subset_iff R I).mpr (fun i => (hc i).2.1),
      fun i => (hc i).2.2⟩
  · rintro ⟨hR, hRI, hw⟩
    apply mem_productDescendants.mpr
    intro i
    exact (source_mem_descendants_width_iff (hd i) (D i) (n i) k (I i) (R i)
      (hI i) (hnk i)).mpr ⟨hR i, (productRectangle_subset_iff R I).mp hRI i, hw i⟩

/-- The paper's strict interior uses sides larger than the cutoff side. -/
theorem source_productInterior_iff
    (hd : ∀ i, 0 < d i) (D : ∀ i, CubeGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubesAtGeneration (n i))
    (hnk : ∀ i, n i ≤ k) (R : ∀ i, Box (Fin (d i))) :
    R ∈ productInterior I (fun i => (k - n i).toNat) ↔
      R ∈ gridRectangles D ∧ productRectangle R ⊆ productRectangle I ∧
        ∀ i u, (2 : ℝ) ^ (-k) < (R i).upper u - (R i).lower u := by
  rw [mem_gridRectangles_iff]
  constructor
  · intro hR
    have hc (i : Fin m) := (source_mem_interior_width_iff (hd i) (D i)
      (n i) k (I i) (R i) (hI i) (hnk i)).mp (mem_productInterior.mp hR i)
    exact ⟨fun i => (hc i).1, (productRectangle_subset_iff R I).mpr (fun i => (hc i).2.1),
      fun i => (hc i).2.2⟩
  · rintro ⟨hR, hRI, hw⟩
    apply mem_productInterior.mpr
    intro i
    exact (source_mem_interior_width_iff (hd i) (D i) (n i) k (I i) (R i)
      (hI i) (hnk i)).mpr ⟨hR i, (productRectangle_subset_iff R I).mp hRI i, hw i⟩

/-- The smallest product cubes are exactly the paper's smallest full cubes. -/
theorem source_productLeaves_iff
    (hd : ∀ i, 0 < d i) (D : ∀ i, CubeGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubesAtGeneration (n i))
    (hnk : ∀ i, n i ≤ k) (R : ∀ i, Box (Fin (d i))) :
    R ∈ productLeaves I (fun i => (k - n i).toNat) ↔
      R ∈ gridRectangles D ∧ productRectangle R ⊆ productRectangle I ∧
        ∀ i u, (R i).upper u - (R i).lower u = (2 : ℝ) ^ (-k) := by
  rw [mem_gridRectangles_iff]
  constructor
  · intro hR
    have hc (i : Fin m) := (source_mem_leaves_width_iff (hd i) (D i)
      (n i) k (I i) (R i) (hI i) (hnk i)).mp (Fintype.mem_piFinset.mp hR i)
    exact ⟨fun i => (hc i).1, (productRectangle_subset_iff R I).mpr (fun i => (hc i).2.1),
      fun i => (hc i).2.2⟩
  · rintro ⟨hR, hRI, hw⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    exact (source_mem_leaves_width_iff (hd i) (D i) (n i) k (I i) (R i)
      (hI i) (hnk i)).mpr ⟨hR i, (productRectangle_subset_iff R I).mp hRI i, hw i⟩

/-- The finite step-function condition is exactly pointwise constancy on the
smallest cubes. -/
theorem source_productLeafConstant_iff
    (hd : ∀ i, 0 < d i) (D : ∀ i, CubeGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubesAtGeneration (n i))
    (hnk : ∀ i, n i ≤ k) (f : ProductPoint d → ℝ) :
    ProductLeafConstant I (fun i => (k - n i).toNat) f ↔
      ∀ R, (R ∈ gridRectangles D ∧ productRectangle R ⊆ productRectangle I ∧
        ∀ i u, (R i).upper u - (R i).lower u = (2 : ℝ) ^ (-k)) →
        ∀ x ∈ productRectangle R, ∀ y ∈ productRectangle R, f x = f y := by
  constructor
  · intro hf R hR
    exact hf R ((source_productLeaves_iff hd D n k I hI hnk R).mpr hR)
  · intro hf R hR
    exact hf R ((source_productLeaves_iff hd D n k I hI hnk R).mp hR)

/-- A nonempty family at the prescribed scales forces cutoff compatibility in every
coordinate. Otherwise the original maximal function has an empty indexing family;
truncating a negative scale gap would change that family. -/
theorem source_cutoff_or_empty
    (hd : ∀ i, 0 < d i) (D : ∀ i, CubeGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubesAtGeneration (n i))
    (G : Finset (∀ i, Box (Fin (d i))))
    (hG : ∀ R ∈ G, R ∈ gridRectangles D ∧ productRectangle R ⊆ productRectangle I ∧
      ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u) :
    (∀ i, n i ≤ k) ∨ G = ∅ := by
  by_cases he : G = ∅
  · exact Or.inr he
  · apply Or.inl
    obtain ⟨R, hR⟩ := Finset.nonempty_iff_ne_empty.mpr he
    obtain ⟨_, hRI, hw⟩ := hG R hR
    intro i
    let u : Fin (d i) := ⟨0, hd i⟩
    have hb := Box.le_iff_bounds.mp ((productRectangle_subset_iff R I).mp hRI i)
    have hwidth : (2 : ℝ) ^ (-k) ≤ (I i).upper u - (I i).lower u :=
      (hw i u).trans (sub_le_sub (hb.2 u) (hb.1 u))
    rw [(D i).width (n i) (I i) (hI i) u] at hwidth
    have hneg := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hwidth
    omega

end ReyZygmund.Geometry
