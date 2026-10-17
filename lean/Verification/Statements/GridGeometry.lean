import ReyZygmund.Geometry.GridFamilies

open BoxIntegral
open scoped Classical

open ReyZygmund.MathlibOnly (CubeGrid gridRectangles)

namespace ReyZygmundVerification

open ReyZygmund.Geometry ReyZygmund.Projection

def gridAllCubesCountableContract : Prop :=
  ∀ {d : ℕ} (D : CubeGrid d), (⋃ n : ℤ, D.cubesAtGeneration n).Countable

def gridLocalDescendantsContract : Prop :=
  ∀ {d : ℕ} (D : CubeGrid d) {n : ℤ} {I Q : Box (Fin d)} {N : ℕ},
  I ∈ D.cubesAtGeneration n →
    (Q ∈ level I N ↔ Q ∈ D.cubesAtGeneration (n + (N : ℤ)) ∧ Q ≤ I)

def gridAncestorContract : Prop :=
  ∀ {d : ℕ} (D : CubeGrid d) {n k : ℤ} {Q : Box (Fin d)},
  Q ∈ D.cubesAtGeneration n → k ≤ n → ∃ I ∈ D.cubesAtGeneration k, Q ≤ I

def productGridCountableContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, CubeGrid (d i)),
    (gridRectangles D).Countable

def productGridFiniteRootsContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, CubeGrid (d i))
    (G : Finset (∀ i, Box (Fin (d i)))), ↑G ⊆ gridRectangles D →
    ∃ (k : ℤ) (N : ℕ) (T : Finset (∀ i, Box (Fin (d i)))),
      (∀ R ∈ T, ∀ i, R i ∈ (D i).cubesAtGeneration k) ∧
      Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
        (fun R S => Disjoint (productRectangle R) (productRectangle S)) ∧
      (∀ Q ∈ G, ∃ R ∈ T, ∀ i, Q i ≤ R i) ∧
      (∀ R ∈ T, G.filter (fun Q => ∀ i, Q i ≤ R i) ⊆
        productDescendants R (fun _ => N))

end ReyZygmundVerification
