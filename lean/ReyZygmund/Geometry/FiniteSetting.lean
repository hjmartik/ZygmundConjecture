import ReyZygmund.Geometry.GridDescendants

/-! # Finite grids with a prescribed smallest scale

A top cube of side `2^l` reaches the smallest side `2^(-k)` after `l + k`
midpoint subdivisions. The cubes and constancy conditions in the specification
therefore agree with the finite partitions used in the proofs. Identifying the
interior cubes requires positive dimension, so that side lengths determine
their scale.
-/

open BoxIntegral MeasureTheory
open scoped Classical

namespace ReyZygmund.MathlibOnly.CubeGrid

/-- Containment orders the side-length exponents when the dimension is positive. -/
theorem sideExponent_le_of_le {d : ℕ} (D : CubeGrid d) (hd : 0 < d)
    {a b : ℤ} {Q R : Box (Fin d)} (hQ : Q ∈ D.cubes a) (hR : R ∈ D.cubes b)
    (hQR : Q ≤ R) : a ≤ b := by
  let i : Fin d := ⟨0, hd⟩
  have hb := Box.le_iff_bounds.mp hQR
  have hw : Q.upper i - Q.lower i ≤ R.upper i - R.lower i :=
    sub_le_sub (hb.2 i) (hb.1 i)
  rw [D.side_length a Q hQ i, D.side_length b R hR i] at hw
  exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hw

end ReyZygmund.MathlibOnly.CubeGrid

namespace ReyZygmund.Geometry

open MathlibOnly (CubeGrid bottomCubes interiorCubes ConstantOnBottomCubes)

/-- The smallest cubes are exactly the cubes of the bottom generation contained
in the top cube. The two generations may agree. -/
theorem common_cutoff_leaves_iff {d : ℕ}
    (D : CubeGrid d) (n k : ℤ) (I Q : Box (Fin d))
    (hI : I ∈ D.cubesAtGeneration n) (hnk : n ≤ k) :
    Q ∈ leaves I (k - n).toNat ↔ Q ∈ D.cubesAtGeneration k ∧ Q ≤ I := by
  have hcut : n + ((k - n).toNat : ℤ) = k := by omega
  rw [mem_leaves, D.mem_level_iff hI, hcut]

variable {d : ℕ} (D : CubeGrid d) {I : Box (Fin d)} {l k : ℤ}

/-- Cubes at the prescribed bottom scale form the last subdivision of the top cube. -/
theorem bottomCubes_eq_leaves (hI : I ∈ D.cubes l) (hcut : -k ≤ l) :
    bottomCubes D I k = (leaves I (l + k).toNat : Set (Box (Fin d))) := by
  have htop : I ∈ D.cubesAtGeneration (-l) := by
    simpa only [MathlibOnly.CubeGrid.cubesAtGeneration, neg_neg] using hI
  ext Q
  change (Q ∈ D.cubesAtGeneration k ∧ Q ≤ I) ↔ Q ∈ leaves I _
  simpa only [sub_neg_eq_add, add_comm] using
    (common_cutoff_leaves_iff D (-l) k I Q htop (by omega)).symm

/-- The difference indices are the subdivisions strictly before the bottom level. -/
theorem interiorCubes_eq_interior (hd : 0 < d) (hI : I ∈ D.cubes l)
    (hcut : -k ≤ l) :
    interiorCubes D I k = (interior I (l + k).toNat : Set (Box (Fin d))) := by
  have htop : I ∈ D.cubesAtGeneration (-l) := by
    simpa only [MathlibOnly.CubeGrid.cubesAtGeneration, neg_neg] using hI
  have hdepth : ((l + k).toNat : ℤ) = l + k := by omega
  ext Q
  change ((∃ a : ℤ, -k < a ∧ Q ∈ D.cubes a) ∧
    (Q : Set (Fin d → ℝ)) ⊆ I) ↔ Q ∈ interior I _
  constructor
  · rintro ⟨⟨a, hka, hQa⟩, hQI⟩
    have hal := D.sideExponent_le_of_le hd hQa hI hQI
    have hindex : -l + ((l - a).toNat : ℤ) = -a := by omega
    refine mem_interior.mpr ⟨(l - a).toNat, by omega, ?_⟩
    apply (D.mem_level_iff htop).mpr
    refine ⟨?_, hQI⟩
    simpa only [hindex, MathlibOnly.CubeGrid.cubesAtGeneration, neg_neg] using hQa
  · intro hQ
    obtain ⟨r, hr, hQr⟩ := mem_interior.mp hQ
    have hgen := D.mem_cubes_of_mem_level htop hQr
    refine ⟨⟨l - (r : ℤ), by omega, ?_⟩, (level I r).le_of_mem hQr⟩
    simpa only [MathlibOnly.CubeGrid.cubesAtGeneration, neg_add_rev, neg_neg,
      sub_eq_add_neg, add_comm] using hgen

/-- Constancy on bottom cubes is precisely constancy on the last finite partition. -/
theorem constantOnBottomCubes_iff (hI : I ∈ D.cubes l) (hcut : -k ≤ l)
    (u : (Fin d → ℝ) → ℝ) :
    ConstantOnBottomCubes D I k u ↔
      ∀ Q ∈ leaves I (l + k).toNat, ∀ x ∈ Q, ∀ y ∈ Q, u x = u y := by
  unfold ConstantOnBottomCubes
  rw [bottomCubes_eq_leaves D hI hcut]
  rfl

/-- Bottom-cube constancy supplies integrability on the top cube. -/
theorem integrableOn_of_constantOnBottomCubes (hI : I ∈ D.cubes l) (hcut : -k ≤ l)
    (u : (Fin d → ℝ) → ℝ) (hu : ConstantOnBottomCubes D I k u) :
    IntegrableOn u (I : Set (Fin d → ℝ)) volume :=
  integrableOn_of_leafConstant I (l + k).toNat u
    ((constantOnBottomCubes_iff D hI hcut u).mp hu)

end ReyZygmund.Geometry
