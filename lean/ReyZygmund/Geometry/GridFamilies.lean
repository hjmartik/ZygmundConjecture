import ReyZygmund.Geometry.GridDescendants
import ReyZygmund.Projection.AveragingRectangles
import Mathlib.Data.Finset.Max

/-! # Finite families in product dyadic grids

The grid rectangles form a countable set. Every finite family is contained in
finitely many disjoint top rectangles at a common scale, with a common smallest
scale.
-/

open BoxIntegral
open scoped Classical

open ReyZygmund.MathlibOnly (CubeGrid gridRectangles)

namespace ReyZygmund.Geometry

open Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- Membership in the product grid can also be indexed by generation,
the negative of the side-length exponent. -/
theorem mem_gridRectangles_iff (D : ∀ i, CubeGrid (d i))
    (Q : ∀ i, Box (Fin (d i))) :
    Q ∈ gridRectangles D ↔ ∀ i, ∃ n : ℤ, Q i ∈ (D i).cubesAtGeneration n := by
  simp only [gridRectangles, Set.mem_ofPred_eq, CubeGrid.mem_all_generations_iff]

theorem countable_gridRectangles (D : ∀ i, CubeGrid (d i)) :
    (gridRectangles D).Countable := by
  simpa only [gridRectangles, Set.mem_iUnion, CubeGrid.mem_all_generations_iff] using
    Set.countable_pi (fun i => (D i).countable_all_cubes)

/-- Localize in disjoint top rectangles, including the top cubes among the retained
scales. -/
theorem exists_finite_grid_roots (D : ∀ i, CubeGrid (d i))
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : ↑G ⊆ gridRectangles D) :
    ∃ (k : ℤ) (N : ℕ) (T : Finset (∀ i, Box (Fin (d i)))),
      (∀ R ∈ T, ∀ i, R i ∈ (D i).cubesAtGeneration k) ∧
      Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
        (fun R S => Disjoint (productRectangle R) (productRectangle S)) ∧
      (∀ Q ∈ G, ∃ R ∈ T, ∀ i, Q i ≤ R i) ∧
      (∀ R ∈ T, G.filter (fun Q => ∀ i, Q i ≤ R i) ⊆
        productDescendants R (fun _ => N)) := by
  have hgen (Q : {Q // Q ∈ G}) (i : Fin m) : ∃ n : ℤ, Q.1 i ∈ (D i).cubesAtGeneration n :=
    (mem_gridRectangles_iff D Q.1).mp (hG Q.2) i
  choose n hn using hgen
  let L : Finset ℤ := insert 0 (G.attach.biUnion fun Q => Finset.univ.image (n Q))
  have hL : L.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  let k := L.min' hL
  let l := L.max' hL
  have hnL (Q : {Q // Q ∈ G}) (i : Fin m) : n Q i ∈ L := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_biUnion.mpr ⟨Q, Finset.mem_attach G Q,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hkn (Q : {Q // Q ∈ G}) (i : Fin m) : k ≤ n Q i := L.min'_le _ (hnL Q i)
  have hnl (Q : {Q // Q ∈ G}) (i : Fin m) : n Q i ≤ l := L.le_max' _ (hnL Q i)
  have hanc (Q : {Q // Q ∈ G}) : ∃ R : ∀ i, Box (Fin (d i)),
      (∀ i, R i ∈ (D i).cubesAtGeneration k) ∧ (∀ i, Q.1 i ≤ R i) := by
    have hi (i : Fin m) := (D i).exists_ancestor (hn Q i) (hkn Q i)
    choose R hR hQR using hi
    exact ⟨R, hR, hQR⟩
  choose R hR hQR using hanc
  let T := G.attach.image R
  have hT (S : ∀ i, Box (Fin (d i))) (hS : S ∈ T) (i : Fin m) :
      S i ∈ (D i).cubesAtGeneration k := by
    obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hS
    exact hR Q i
  refine ⟨k, (l - k).toNat, T, hT, ?_, ?_, ?_⟩
  · intro S hS U hU hne
    apply Set.disjoint_left.mpr
    intro x hxS hxU
    apply hne
    funext i
    exact (D i).eq_of_mem_of_mem (hT S hS i) (hT U hU i)
      ((mem_productRectangle S x).mp hxS i) ((mem_productRectangle U x).mp hxU i)
  · intro Q hQ
    exact ⟨R ⟨Q, hQ⟩, Finset.mem_image.mpr
      ⟨⟨Q, hQ⟩, Finset.mem_attach G _, rfl⟩, hQR ⟨Q, hQ⟩⟩
  · intro S hS Q hQ
    obtain ⟨hQG, hQS⟩ := Finset.mem_filter.mp hQ
    apply mem_productDescendants.mpr
    intro i
    have hn0 := hkn ⟨Q, hQG⟩ i
    have hn1 := hnl ⟨Q, hQG⟩ i
    have hki : k + ((n ⟨Q, hQG⟩ i - k).toNat : ℤ) = n ⟨Q, hQG⟩ i := by omega
    refine mem_descendants.mpr ⟨(n ⟨Q, hQG⟩ i - k).toNat, by omega, ?_⟩
    exact ((D i).mem_level_iff (hT S hS i)).mpr
      ⟨by simpa only [hki] using hn ⟨Q, hQG⟩ i, hQS i⟩

end ReyZygmund.Geometry
