import ReyZygmund.Selection.Variational

/-! Explicit expected propositions for the finite geometric selection.
These contain no analytic shadow-comparison conclusion or grid premise.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical
open ReyZygmund.Geometry ReyZygmund.Overlap

namespace ReyZygmundVerification

def finiteVariationalSelectionContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (F : Finset (∀ i, Box (Fin (d i)))),
    ∃ G : Finset (∀ i, Box (Fin (d i))), G ⊆ F ∧
      (∀ V : Finset (∀ i, Box (Fin (d i))), V ⊆ F →
        2 * volume.real (finiteShadow V) -
            ∑ Q ∈ V, volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ≤
          2 * volume.real (finiteShadow G) -
            ∑ Q ∈ G, volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ))) ∧
      (∀ Q ∈ G,
        volume.real ((flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∩ finiteShadow (G.erase Q)) ≤
          (1 / 2 : ℝ) * volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ))) ∧
      (∀ Q ∈ F,
        (1 / 2 : ℝ) * volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ≤
          volume.real ((flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∩ finiteShadow G))

def finiteVariationalHalfSparseContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ} (F : Finset (∀ i, Box (Fin (d i)))),
    ∃ G : Finset (∀ i, Box (Fin (d i))), G ⊆ F ∧
      (∀ Q ∈ G,
        volume.real ((flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∩ finiteShadow (G.erase Q)) ≤
          (1 / 2 : ℝ) * volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ))) ∧
      (∀ Q ∈ F,
        (1 / 2 : ℝ) * volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ≤
          volume.real ((flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∩ finiteShadow G)) ∧
      ∃ E : (∀ i, Box (Fin (d i))) → Set (Fin (∑ i, d i) → ℝ),
        (∀ Q, E Q = (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) \ finiteShadow (G.erase Q)) ∧
        (∀ Q ∈ G, MeasurableSet (E Q) ∧ E Q ⊆ (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ∧
          (1 / 2 : ℝ) * volume.real (flatProductBox Q : Set (Fin (∑ i, d i) → ℝ)) ≤ volume.real (E Q)) ∧
        Set.Pairwise (↑G : Set (∀ i, Box (Fin (d i))))
          (fun Q R => Disjoint (E Q) (E R))

end ReyZygmundVerification
