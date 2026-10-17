import ReyZygmund.Geometry.FiniteAverages
import ReyZygmund.Geometry.CubeGridChildren
import Mathlib.Topology.Bases

/-! # Constructing dyadic grids from their generations

Generation `n` has side length `2 ^ (-n)`. A partition at each generation,
closed under taking midpoint children, gives a cube grid: iterating the child
partitions proves nesting.
-/

open BoxIntegral
open ReyZygmund.Geometry
open scoped Classical

namespace ReyZygmund.MathlibOnly.CubeGrid

variable {d : ℕ}

private theorem mem_generation_of_mem_level
    (C : ℤ → Set (Box (Fin d)))
    (hchildren : ∀ n Q, Q ∈ C n →
      ∀ R ∈ Prepartition.splitCenter Q, R ∈ C (n + 1))
    {n : ℤ} {I Q : Box (Fin d)} (hI : I ∈ C n)
    {N : ℕ} (hQ : Q ∈ level I N) : Q ∈ C (n + (N : ℤ)) := by
  induction N generalizing Q with
  | zero =>
    have hQI : Q = I := Prepartition.mem_top.mp hQ
    subst Q
    simpa using hI
  | succ N ih =>
    obtain ⟨R, hR, hQR⟩ := (level I N).mem_biUnion.mp hQ
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
      hchildren (n + (N : ℤ)) R (ih hR) Q hQR

private theorem le_of_generation_partitions
    (C : ℤ → Set (Box (Fin d)))
    (hdisjoint : ∀ n, (C n).Pairwise
      (fun Q R => Disjoint (Q : Set (Fin d → ℝ)) (R : Set (Fin d → ℝ))))
    (hchildren : ∀ n Q, Q ∈ C n →
      ∀ R ∈ Prepartition.splitCenter Q, R ∈ C (n + 1))
    {n k : ℤ} {Q R : Box (Fin d)} (hQ : Q ∈ C n) (hR : R ∈ C k)
    (hnk : n ≤ k) {x : Fin d → ℝ} (hxQ : x ∈ Q) (hxR : x ∈ R) : R ≤ Q := by
  obtain ⟨S, hS, hxS⟩ := level_isPartition Q (k - n).toNat x hxQ
  have hindex : n + ((k - n).toNat : ℤ) = k := by omega
  have hSk : S ∈ C k := by
    simpa only [hindex] using mem_generation_of_mem_level C hchildren hQ hS
  have hRS : R = S := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisjoint k hR hSk hne) hxR hxS
  exact hRS ▸ (level Q _).le_of_mem hS

/-- Construct a cube grid from partitions indexed by generation and closed
under midpoint children. The public grid is indexed by side-length exponent. -/
def ofGenerations
    (C : ℤ → Set (Box (Fin d)))
    (hwidth : ∀ n Q, Q ∈ C n → ∀ i,
      Q.upper i - Q.lower i = (2 : ℝ) ^ (-n))
    (hdisjoint : ∀ n, (C n).Pairwise
      (fun Q R => Disjoint (Q : Set (Fin d → ℝ)) (R : Set (Fin d → ℝ))))
    (hcover : ∀ n x, ∃ Q ∈ C n, x ∈ Q)
    (hchildren : ∀ n Q, Q ∈ C n →
      ∀ R ∈ Prepartition.splitCenter Q, R ∈ C (n + 1)) : CubeGrid d where
  cubes k := C (-k)
  side_length k Q hQ i := by simpa only [neg_neg] using hwidth (-k) Q hQ i
  pairwise_disjoint k := hdisjoint (-k)
  covers k := hcover (-k)
  nested k l Q R hQ hR := by
    by_cases hdis : Disjoint (Q : Set (Fin d → ℝ)) (R : Set (Fin d → ℝ))
    · exact Or.inl hdis
    · obtain ⟨x, hxQ, hxR⟩ := Set.not_disjoint_iff.mp hdis
      right
      rcases le_total (-k) (-l) with h | h
      · exact Or.inr (le_of_generation_partitions C hdisjoint hchildren hQ hR h hxQ hxR)
      · exact Or.inl (le_of_generation_partitions C hdisjoint hchildren hR hQ h hxR hxQ)

variable (D : CubeGrid d)

/-- Changing the sign returns from generation indices to side exponents. -/
@[simp] theorem cubesAtGeneration_neg (k : ℤ) :
    D.cubesAtGeneration (-k) = D.cubes k := by
  simp only [cubesAtGeneration, neg_neg]

/-- The two index conventions enumerate the same cubes. -/
theorem mem_all_generations_iff {Q : Box (Fin d)} :
    (∃ n : ℤ, Q ∈ D.cubesAtGeneration n) ↔ ∃ k : ℤ, Q ∈ D.cubes k := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨-n, hn⟩
  · rintro ⟨k, hk⟩
    exact ⟨-k, by simpa only [cubesAtGeneration_neg] using hk⟩

/-- The width formula in generation indices. -/
theorem width (n : ℤ) (Q : Box (Fin d)) (hQ : Q ∈ D.cubesAtGeneration n) (i : Fin d) :
    Q.upper i - Q.lower i = (2 : ℝ) ^ (-n) := D.side_length (-n) Q hQ i

/-- Cubes at a fixed generation are pairwise disjoint. -/
theorem disjoint (n : ℤ) : (D.cubesAtGeneration n).Pairwise
    (fun Q R => Disjoint (Q : Set (Fin d → ℝ)) (R : Set (Fin d → ℝ))) :=
  D.pairwise_disjoint (-n)

/-- Every point belongs to a cube at each generation. -/
theorem cover (n : ℤ) (x : Fin d → ℝ) : ∃ Q ∈ D.cubesAtGeneration n, x ∈ Q :=
  D.covers (-n) x

/-- Midpoint children belong to the next generation. -/
theorem children (n : ℤ) (Q : Box (Fin d)) (hQ : Q ∈ D.cubesAtGeneration n)
    (R : Box (Fin d)) (hR : R ∈ Prepartition.splitCenter Q) :
    R ∈ D.cubesAtGeneration (n + 1) := by
  simpa only [cubesAtGeneration, neg_add_rev, add_comm, sub_eq_add_neg] using D.child_mem hQ hR

end ReyZygmund.MathlibOnly.CubeGrid
