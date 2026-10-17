import ReyZygmund.Geometry.Grids

/-!
# Dyadic grid cubes and finite descendants

Finite descendants are obtained by repeatedly taking dyadic children. A grid cube
has an ancestor at each specified larger scale.
-/

open BoxIntegral
open ReyZygmund.Geometry
open scoped Classical

namespace ReyZygmund.MathlibOnly.CubeGrid

variable {d : ℕ} (D : CubeGrid d)

theorem eq_of_mem_of_mem {n : ℤ} {Q R : Box (Fin d)}
    (hQ : Q ∈ D.cubesAtGeneration n) (hR : R ∈ D.cubesAtGeneration n)
    {x : Fin d → ℝ} (hxQ : x ∈ Q) (hxR : x ∈ R) : Q = R := by
  by_contra hne
  exact Set.disjoint_left.mp (D.disjoint n hQ hR hne) hxQ hxR

/-- Each generation is countable because its open cube interiors are
nonempty and disjoint in Euclidean space. -/
theorem countable_cubes (n : ℤ) : (D.cubesAtGeneration n).Countable := by
  have hdis : (D.cubesAtGeneration n).PairwiseDisjoint (fun Q => Box.Ioo Q) := by
    intro Q hQ R hR hne
    exact (D.disjoint n hQ hR hne).mono Q.Ioo_subset_coe R.Ioo_subset_coe
  apply hdis.countable_of_isOpen
  · intro Q _
    exact isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  · intro Q _
    refine ⟨fun i => (Q.lower i + Q.upper i) / 2, ?_⟩
    intro i _
    constructor <;> linarith [Q.lower_lt_upper i]

/-- The full set of grid cubes is a countable union of generations. -/
theorem countable_all_cubes : (⋃ n : ℤ, D.cubesAtGeneration n).Countable :=
  Set.countable_iUnion (fun n => D.countable_cubes n)

/-- Every finite dyadic descendant belongs to the expected grid
generation. The generation increases as the side length decreases. -/
theorem mem_cubes_of_mem_level {n : ℤ} {I Q : Box (Fin d)}
    (hI : I ∈ D.cubesAtGeneration n) {N : ℕ} (hQ : Q ∈ level I N) :
    Q ∈ D.cubesAtGeneration (n + (N : ℤ)) := by
  induction N generalizing Q with
  | zero =>
    have hQI : Q = I := Prepartition.mem_top.mp hQ
    subst Q
    simpa using hI
  | succ N ih =>
    obtain ⟨R, hR, hQR⟩ := (level I N).mem_biUnion.mp hQ
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
      D.children (n + (N : ℤ)) R (ih hR) Q hQR

/-- A finer grid cube meeting a top cube is one of its descendants at that depth.
-/
theorem mem_level_of_mem_point {n : ℤ} {I Q : Box (Fin d)} {N : ℕ}
    (hI : I ∈ D.cubesAtGeneration n) (hQ : Q ∈ D.cubesAtGeneration (n + (N : ℤ)))
    {x : Fin d → ℝ} (hxI : x ∈ I) (hxQ : x ∈ Q) : Q ∈ level I N := by
  obtain ⟨R, hR, hxR⟩ := level_isPartition I N x hxI
  have hQR := D.eq_of_mem_of_mem hQ (D.mem_cubes_of_mem_level hI hR) hxQ hxR
  exact hQR.symm ▸ hR

/-- The depth-`N` descendants are the cubes at generation `n + N` contained in the
top cube. -/
theorem mem_level_iff {n : ℤ} {I Q : Box (Fin d)} {N : ℕ}
    (hI : I ∈ D.cubesAtGeneration n) :
    Q ∈ level I N ↔ Q ∈ D.cubesAtGeneration (n + (N : ℤ)) ∧ Q ≤ I := by
  constructor
  · intro hQ
    exact ⟨D.mem_cubes_of_mem_level hI hQ, (level I N).le_of_mem hQ⟩
  · rintro ⟨hQ, hQI⟩
    exact D.mem_level_of_mem_point hI hQ (hQI Q.upper_mem) Q.upper_mem

/-- Every cube has an ancestor at each fixed coarser generation. -/
theorem exists_ancestor {n k : ℤ} {Q : Box (Fin d)}
    (hQ : Q ∈ D.cubesAtGeneration n) (hkn : k ≤ n) :
    ∃ I ∈ D.cubesAtGeneration k, Q ≤ I := by
  obtain ⟨I, hI, hxI⟩ := D.cover k Q.upper
  have hnk : k + ((n - k).toNat : ℤ) = n := by omega
  have hlocal : Q ∈ level I (n - k).toNat :=
    D.mem_level_of_mem_point hI (by simpa only [hnk] using hQ) hxI Q.upper_mem
  exact ⟨I, hI, (level I _).le_of_mem hlocal⟩

end ReyZygmund.MathlibOnly.CubeGrid
