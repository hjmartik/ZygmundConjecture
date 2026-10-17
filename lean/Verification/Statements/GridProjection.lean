import ReyZygmund.Geometry.GlobalDifferences
import ReyZygmund.Projection.Properties
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! Independent explicit propositions for the two original projection formulas
and all-scale annihilation. No GridProjection implementation is imported. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

open ReyZygmund.MathlibOnly (CubeGrid gridRectangles)

namespace ReyZygmundVerification

open ReyZygmund.Geometry ReyZygmund.Projection

def gridCutoffAncestorContract : Prop :=
  ∀ (e : ℕ) (D : CubeGrid e) (n a : ℤ) (I Q : Box (Fin e)) (N : ℕ),
    I ∈ D.cubesAtGeneration n → Q ∈ D.cubesAtGeneration a → Q ≤ I → n + (N : ℤ) ≤ a →
      ∃ P, P ∈ level I N ∧ Q ≤ P

def gridCutoffDifferenceZeroContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (D : ∀ i, CubeGrid (d i)) (n : Fin m → ℤ)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
    (∀ j, I j ∈ (D j).cubesAtGeneration (n j)) → ∀ (F : boundedMeasurableFunctions d),
      ProductLeafConstant I N F.1 → (∀ x, x ∉ productRectangle I → F.1 x = 0) →
      ∀ (L : ∀ i, Box (Fin (d i))) (i : Fin m) (a : ℤ),
        L i ∈ (D i).cubesAtGeneration a → L i ≤ I i → n i + (N i : ℤ) ≤ a →
          rawProductDifference L F.1 = 0

def gridRemovedDifferenceHasSumContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ), (∀ i, 0 < d i) →
    ∀ (D : ∀ i, CubeGrid (d i)) (n : Fin m → ℤ)
      (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
      (∀ j, I j ∈ (D j).cubesAtGeneration (n j)) →
      ∀ (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
      ∀ (F : boundedMeasurableFunctions d),
        ProductLeafConstant I N F.1 → (∀ x, x ∉ productRectangle I → F.1 x = 0) →
        (Function.support (fun L : {L : ∀ i, Box (Fin (d i)) //
            L ∈ gridRectangles D ∧ ∃ J ∈ G, productRectangle L ⊆ productRectangle J} =>
          rawProductDifference L.1 F.1)).Finite ∧
        HasSum (fun L : {L : ∀ i, Box (Fin (d i)) //
            L ∈ gridRectangles D ∧ ∃ J ∈ G, productRectangle L ⊆ productRectangle J} =>
          rawProductDifference L.1 F.1)
          (F.1 - (finiteProjectionMap I N G F).1)

def gridProjectionFormulaContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ), (∀ i, 0 < d i) →
    ∀ (D : ∀ i, CubeGrid (d i)) (n : Fin m → ℤ)
      (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
      (∀ j, I j ∈ (D j).cubesAtGeneration (n j)) →
      ∀ (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
      ∀ (F : boundedMeasurableFunctions d),
        ProductLeafConstant I N F.1 → (∀ x, x ∉ productRectangle I → F.1 x = 0) →
        (finiteProjectionMap I N G F).1 = F.1 -
          ∑' L : {L : ∀ i, Box (Fin (d i)) //
            L ∈ gridRectangles D ∧ ∃ J ∈ G, productRectangle L ⊆ productRectangle J},
            rawProductDifference L.1 F.1

def gridProjectionAnnihilationContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ), (∀ i, 0 < d i) →
    ∀ (D : ∀ i, CubeGrid (d i)) (n : Fin m → ℤ)
      (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ),
      (∀ j, I j ∈ (D j).cubesAtGeneration (n j)) →
      ∀ (G : Finset (∀ i, Box (Fin (d i)))), G ⊆ productDescendants I N →
      ∀ (F : boundedMeasurableFunctions d),
        ProductLeafConstant I N F.1 → (∀ x, x ∉ productRectangle I → F.1 x = 0) →
        ∀ (L : ∀ i, Box (Fin (d i))), L ∈ gridRectangles D →
          (∃ J ∈ G, productRectangle L ⊆ productRectangle J) →
          rawProductDifference L (finiteProjectionMap I N G F).1 = 0

end ReyZygmundVerification
