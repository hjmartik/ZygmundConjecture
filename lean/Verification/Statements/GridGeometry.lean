import ReyZygmund.Geometry.GridFamilies

open BoxIntegral
open scoped Classical

namespace ReyZygmundVerification

open ReyZygmund.Geometry ReyZygmund.Projection

def gridAllCubesCountableContract : Prop :=
  ∀ {d : ℕ} (D : DyadicGrid d), (⋃ n : ℤ, D.cubes n).Countable

def gridLocalDescendantsContract : Prop :=
  ∀ {d : ℕ} (D : DyadicGrid d) {n : ℤ} {I Q : Box (Fin d)} {N : ℕ},
  I ∈ D.cubes n →
    (Q ∈ level I N ↔ Q ∈ D.cubes (n + (N : ℤ)) ∧ Q ≤ I)

def gridAncestorContract : Prop :=
  ∀ {d : ℕ} (D : DyadicGrid d) {n k : ℤ} {Q : Box (Fin d)},
  Q ∈ D.cubes n → k ≤ n → ∃ I ∈ D.cubes k, Q ≤ I

def productGridCountableContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, DyadicGrid (d i)),
    (gridRectangles D).Countable

def productGridFiniteRootsContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (D : ∀ i, DyadicGrid (d i))
    (G : Finset (∀ i, Box (Fin (d i)))), ↑G ⊆ gridRectangles D →
    ∃ (k : ℤ) (N : ℕ) (T : Finset (∀ i, Box (Fin (d i)))),
      (∀ R ∈ T, ∀ i, R i ∈ (D i).cubes k) ∧
      Set.Pairwise (↑T : Set (∀ i, Box (Fin (d i))))
        (fun R S => Disjoint (productBox R) (productBox S)) ∧
      (∀ Q ∈ G, ∃ R ∈ T, ∀ i, Q i ≤ R i) ∧
      (∀ R ∈ T, G.filter (fun Q => ∀ i, Q i ≤ R i) ⊆
        productDescendants R (fun _ => N))

end ReyZygmundVerification
