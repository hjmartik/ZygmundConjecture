import ReyZygmund.Geometry.Grids

/-!
# From an arbitrary grid to the concrete finite cube construction

The finite descendants are obtained by repeatedly taking dyadic children. These
lemmas do not require a common ancestor for the entire grid or for an arbitrary
finite family. An ancestor is chosen only at a specified larger scale.
-/

open BoxIntegral
open scoped Classical

namespace ReyZygmund.Geometry.DyadicGrid

variable {d : ℕ} (D : DyadicGrid d)

theorem eq_of_mem_of_mem {n : ℤ} {Q R : Box (Fin d)}
    (hQ : Q ∈ D.cubes n) (hR : R ∈ D.cubes n)
    {x : Fin d → ℝ} (hxQ : x ∈ Q) (hxR : x ∈ R) : Q = R := by
  by_contra hne
  exact Set.disjoint_left.mp (D.disjoint n hQ hR hne) hxQ hxR

/-- Each generation is countable because its open cube interiors are
nonempty and disjoint in Euclidean space. Countability is not a grid field. -/
theorem countable_cubes (n : ℤ) : (D.cubes n).Countable := by
  have hdis : (D.cubes n).PairwiseDisjoint (fun Q => Box.Ioo Q) := by
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
theorem countable_all_cubes : (⋃ n : ℤ, D.cubes n).Countable :=
  Set.countable_iUnion (fun n => D.countable_cubes n)

/-- Every finite dyadic descendant belongs to the expected grid
generation. The generation increases as the side length decreases. -/
theorem mem_cubes_of_mem_level {n : ℤ} {I Q : Box (Fin d)}
    (hI : I ∈ D.cubes n) {N : ℕ} (hQ : Q ∈ level I N) :
    Q ∈ D.cubes (n + (N : ℤ)) := by
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
    (hI : I ∈ D.cubes n) (hQ : Q ∈ D.cubes (n + (N : ℤ)))
    {x : Fin d → ℝ} (hxI : x ∈ I) (hxQ : x ∈ Q) : Q ∈ level I N := by
  obtain ⟨R, hR, hxR⟩ := level_isPartition I N x hxI
  have hQR := D.eq_of_mem_of_mem hQ (D.mem_cubes_of_mem_level hI hR) hxQ hxR
  exact hQR.symm ▸ hR

/-- Exact dictionary, including depth zero and the half-open boundary points. -/
theorem mem_level_iff {n : ℤ} {I Q : Box (Fin d)} {N : ℕ}
    (hI : I ∈ D.cubes n) :
    Q ∈ level I N ↔ Q ∈ D.cubes (n + (N : ℤ)) ∧ Q ≤ I := by
  constructor
  · intro hQ
    exact ⟨D.mem_cubes_of_mem_level hI hQ, (level I N).le_of_mem hQ⟩
  · rintro ⟨hQ, hQI⟩
    exact D.mem_level_of_mem_point hI hQ (hQI Q.upper_mem) Q.upper_mem

/-- Every cube has an ancestor at each fixed coarser generation. This asserts
no common ancestor at infinity for cubes lying in different components. -/
theorem exists_ancestor {n k : ℤ} {Q : Box (Fin d)}
    (hQ : Q ∈ D.cubes n) (hkn : k ≤ n) :
    ∃ I ∈ D.cubes k, Q ≤ I := by
  obtain ⟨I, hI, hxI⟩ := D.cover k Q.upper
  have hnk : k + ((n - k).toNat : ℤ) = n := by omega
  have hlocal : Q ∈ level I (n - k).toNat :=
    D.mem_level_of_mem_point hI (by simpa only [hnk] using hQ) hxI Q.upper_mem
  exact ⟨I, hI, (level I _).le_of_mem hlocal⟩

end ReyZygmund.Geometry.DyadicGrid
