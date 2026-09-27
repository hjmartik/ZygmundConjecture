import ReyZygmund.Geometry.RoundedSlices

open BoxIntegral

namespace ReyZygmundVerification

open ReyZygmund.Geometry

def gridContainmentOrderContract : Prop :=
  ∀ {d : ℕ} (D : DyadicGrid d) {n k : ℤ} {Q R : Box (Fin d)},
    Q ∈ D.cubes n → R ∈ D.cubes k → n ≤ k →
    ∀ {x : Fin d → ℝ}, x ∈ Q → x ∈ R → R ≤ Q

def gridStrictGenerationContract : Prop :=
  ∀ {d : ℕ} (D : DyadicGrid d) {n k : ℤ} {Q R : Box (Fin d)},
    Q ∈ D.cubes n → R ∈ D.cubes k → Q ≤ R → Q ≠ R → k < n

def roundedScaleOrderContract : Prop :=
  ∀ {n : ℕ} (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)),
    Monotone phi →
    ∀ {k l : Fin (n + 1) → ℤ}, k ∈ roundedScales phi → l ∈ roundedScales phi →
      (∀ i : Fin n, k i.castSucc < l i.castSucc) →
        k (Fin.last n) ≤ l (Fin.last n)

def sliceProjectionInjectivityContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ} (D : ∀ i, DyadicGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))),
    G ⊆ gridRectangles D →
    (∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S) →
    ∀ t : Fin (d (Fin.last n)) → ℝ,
      Set.InjOn initialProjection {R | R ∈ G ∧ t ∈ R (Fin.last n)}

def roundedSliceWeakerContainmentContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}, 0 < n →
    ∀ (D : ∀ i, DyadicGrid (d i))
      (phi : (Fin n → Set.Ioi (0 : ℝ)) → Set.Ioi (0 : ℝ)),
      Monotone phi →
      ∀ G : Set (∀ i, Box (Fin (d i))), G ⊆ roundedGridRectangles D phi →
        (∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S) →
        ∀ t : Fin (d (Fin.last n)) → ℝ,
          ∀ P ∈ sliceFamily G t, ∀ Q ∈ sliceFamily G t,
            (∀ i, P i ≤ Q i) → ∃ i, P i = Q i

end ReyZygmundVerification
