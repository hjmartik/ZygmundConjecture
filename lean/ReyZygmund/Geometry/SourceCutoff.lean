import ReyZygmund.Geometry.GridFamilies
import ReyZygmund.Geometry.ProductContainment

/-! # A common smallest side length

For a top cube at generation `n i`, the smallest side `2^(-k)` corresponds to
dyadic depth `(k - n i).toNat`. The set and constancy identities are pointwise,
on arbitrary supplied dyadic grids.

-/

open BoxIntegral
open scoped Classical

namespace ReyZygmund.Geometry

open Projection

private theorem source_generation_le_of_le {e : ℕ} (he : 0 < e)
    (D : DyadicGrid e) {a b : ℤ} {Q R : Box (Fin e)}
    (hQ : Q ∈ D.cubes a) (hR : R ∈ D.cubes b) (hQR : Q ≤ R) : b ≤ a := by
  let i : Fin e := ⟨0, he⟩
  have hb := Box.le_iff_bounds.mp hQR
  have hw : Q.upper i - Q.lower i ≤ R.upper i - R.lower i :=
    sub_le_sub (hb.2 i) (hb.1 i)
  rw [D.width a Q hQ i, D.width b R hR i] at hw
  have hneg := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hw
  omega

private theorem source_mem_descendants_width_iff {e : ℕ} (he : 0 < e)
    (D : DyadicGrid e) (n k : ℤ) (I Q : Box (Fin e))
    (hI : I ∈ D.cubes n) (hnk : n ≤ k) :
    Q ∈ descendants I (k - n).toNat ↔
      (∃ a, Q ∈ D.cubes a) ∧ Q ≤ I ∧
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
    have hna := source_generation_le_of_le he D hQa hI hQI
    have hwidth := hw ⟨0, he⟩
    rw [D.width a Q hQa] at hwidth
    have hak := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hwidth
    have hindex : n + ((a - n).toNat : ℤ) = a := by omega
    refine mem_descendants.mpr ⟨(a - n).toNat, by omega, ?_⟩
    exact (D.mem_level_iff hI).mpr ⟨by simpa only [hindex] using hQa, hQI⟩

private theorem source_mem_interior_width_iff {e : ℕ} (he : 0 < e)
    (D : DyadicGrid e) (n k : ℤ) (I Q : Box (Fin e))
    (hI : I ∈ D.cubes n) (hnk : n ≤ k) :
    Q ∈ interior I (k - n).toNat ↔
      (∃ a, Q ∈ D.cubes a) ∧ Q ≤ I ∧
        ∀ u, (2 : ℝ) ^ (-k) < Q.upper u - Q.lower u := by
  have hcut : n + ((k - n).toNat : ℤ) = k := by omega
  constructor
  · intro hQ
    obtain ⟨r, hr, hQr⟩ := mem_interior.mp hQ
    have hgen := D.mem_cubes_of_mem_level hI hQr
    refine ⟨⟨n + (r : ℤ), hgen⟩, (level I r).le_of_mem hQr, ?_⟩
    intro u
    rw [D.width _ Q hgen u]
    apply (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr
    omega
  · rintro ⟨⟨a, hQa⟩, hQI, hw⟩
    have hna := source_generation_le_of_le he D hQa hI hQI
    have hwidth := hw ⟨0, he⟩
    rw [D.width a Q hQa] at hwidth
    have hak := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hwidth
    have hindex : n + ((a - n).toNat : ℤ) = a := by omega
    refine mem_interior.mpr ⟨(a - n).toNat, by omega, ?_⟩
    exact (D.mem_level_iff hI).mpr ⟨by simpa only [hindex] using hQa, hQI⟩

private theorem source_mem_leaves_width_iff {e : ℕ} (he : 0 < e)
    (D : DyadicGrid e) (n k : ℤ) (I Q : Box (Fin e))
    (hI : I ∈ D.cubes n) (hnk : n ≤ k) :
    Q ∈ leaves I (k - n).toNat ↔
      (∃ a, Q ∈ D.cubes a) ∧ Q ≤ I ∧
        ∀ u, Q.upper u - Q.lower u = (2 : ℝ) ^ (-k) := by
  have hcut : n + ((k - n).toNat : ℤ) = k := by omega
  constructor
  · intro hQ
    have hlevel := mem_leaves.mp hQ
    have hgen : Q ∈ D.cubes k := by
      simpa only [hcut] using D.mem_cubes_of_mem_level hI hlevel
    exact ⟨⟨k, hgen⟩, (level I _).le_of_mem hlevel, D.width k Q hgen⟩
  · rintro ⟨⟨a, hQa⟩, hQI, hw⟩
    have hwidth := hw ⟨0, he⟩
    rw [D.width a Q hQa] at hwidth
    have hneg := (zpow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).injective hwidth
    have hak : a = k := by omega
    subst a
    apply mem_leaves.mpr
    exact (D.mem_level_iff hI).mpr ⟨by simpa only [hcut] using hQa, hQI⟩

variable {m : ℕ} {d : Fin m → ℕ}

/-- The paper's full finite family, including cubes of the cutoff side. -/
theorem source_productDescendants_iff
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubes (n i))
    (hnk : ∀ i, n i ≤ k) (R : ∀ i, Box (Fin (d i))) :
    R ∈ productDescendants I (fun i => (k - n i).toNat) ↔
      R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
        ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u := by
  constructor
  · intro hR
    have hc (i : Fin m) := (source_mem_descendants_width_iff (hd i) (D i)
      (n i) k (I i) (R i) (hI i) (hnk i)).mp (mem_productDescendants.mp hR i)
    exact ⟨fun i => (hc i).1, (productBox_subset_iff R I).mpr (fun i => (hc i).2.1),
      fun i => (hc i).2.2⟩
  · rintro ⟨hR, hRI, hw⟩
    apply mem_productDescendants.mpr
    intro i
    exact (source_mem_descendants_width_iff (hd i) (D i) (n i) k (I i) (R i)
      (hI i) (hnk i)).mpr ⟨hR i, (productBox_subset_iff R I).mp hRI i, hw i⟩

/-- The paper's strict interior uses sides larger than the cutoff side. -/
theorem source_productInterior_iff
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubes (n i))
    (hnk : ∀ i, n i ≤ k) (R : ∀ i, Box (Fin (d i))) :
    R ∈ productInterior I (fun i => (k - n i).toNat) ↔
      R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
        ∀ i u, (2 : ℝ) ^ (-k) < (R i).upper u - (R i).lower u := by
  constructor
  · intro hR
    have hc (i : Fin m) := (source_mem_interior_width_iff (hd i) (D i)
      (n i) k (I i) (R i) (hI i) (hnk i)).mp (mem_productInterior.mp hR i)
    exact ⟨fun i => (hc i).1, (productBox_subset_iff R I).mpr (fun i => (hc i).2.1),
      fun i => (hc i).2.2⟩
  · rintro ⟨hR, hRI, hw⟩
    apply mem_productInterior.mpr
    intro i
    exact (source_mem_interior_width_iff (hd i) (D i) (n i) k (I i) (R i)
      (hI i) (hnk i)).mpr ⟨hR i, (productBox_subset_iff R I).mp hRI i, hw i⟩

/-- The smallest product cubes are exactly the paper's smallest full cubes. -/
theorem source_productLeaves_iff
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubes (n i))
    (hnk : ∀ i, n i ≤ k) (R : ∀ i, Box (Fin (d i))) :
    R ∈ productLeaves I (fun i => (k - n i).toNat) ↔
      R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
        ∀ i u, (R i).upper u - (R i).lower u = (2 : ℝ) ^ (-k) := by
  constructor
  · intro hR
    have hc (i : Fin m) := (source_mem_leaves_width_iff (hd i) (D i)
      (n i) k (I i) (R i) (hI i) (hnk i)).mp (Fintype.mem_piFinset.mp hR i)
    exact ⟨fun i => (hc i).1, (productBox_subset_iff R I).mpr (fun i => (hc i).2.1),
      fun i => (hc i).2.2⟩
  · rintro ⟨hR, hRI, hw⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    exact (source_mem_leaves_width_iff (hd i) (D i) (n i) k (I i) (R i)
      (hI i) (hnk i)).mpr ⟨hR i, (productBox_subset_iff R I).mp hRI i, hw i⟩

/-- The finite step-function condition is exactly pointwise constancy on the smallest
cubes; values outside the top rectangle are unrestricted. -/
theorem source_productLeafConstant_iff
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubes (n i))
    (hnk : ∀ i, n i ≤ k) (f : ProductPoint d → ℝ) :
    ProductLeafConstant I (fun i => (k - n i).toNat) f ↔
      ∀ R, (R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
        ∀ i u, (R i).upper u - (R i).lower u = (2 : ℝ) ^ (-k)) →
        ∀ x ∈ productBox R, ∀ y ∈ productBox R, f x = f y := by
  constructor
  · intro hf R hR
    exact hf R ((source_productLeaves_iff hd D n k I hI hnk R).mpr hR)
  · intro hf R hR
    exact hf R ((source_productLeaves_iff hd D n k I hI hnk R).mp hR)

/-- A nonempty source family forces cutoff compatibility in every coordinate.
Otherwise the original maximal function has an empty indexing family; that
case must not be passed through a depth obtained by truncating a negative gap. -/
theorem source_cutoff_or_empty
    (hd : ∀ i, 0 < d i) (D : ∀ i, DyadicGrid (d i)) (n : Fin m → ℤ) (k : ℤ)
    (I : ∀ i, Box (Fin (d i))) (hI : ∀ i, I i ∈ (D i).cubes (n i))
    (G : Finset (∀ i, Box (Fin (d i))))
    (hG : ∀ R ∈ G, R ∈ gridRectangles D ∧ productBox R ⊆ productBox I ∧
      ∀ i u, (2 : ℝ) ^ (-k) ≤ (R i).upper u - (R i).lower u) :
    (∀ i, n i ≤ k) ∨ G = ∅ := by
  by_cases he : G = ∅
  · exact Or.inr he
  · apply Or.inl
    obtain ⟨R, hR⟩ := Finset.nonempty_iff_ne_empty.mpr he
    obtain ⟨_, hRI, hw⟩ := hG R hR
    intro i
    let u : Fin (d i) := ⟨0, hd i⟩
    have hb := Box.le_iff_bounds.mp ((productBox_subset_iff R I).mp hRI i)
    have hwidth : (2 : ℝ) ^ (-k) ≤ (I i).upper u - (I i).lower u :=
      (hw i u).trans (sub_le_sub (hb.2 u) (hb.1 u))
    rw [(D i).width (n i) (I i) (hI i) u] at hwidth
    have hneg := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hwidth
    omega

end ReyZygmund.Geometry
