import ReyZygmund.Geometry.GridProductAlgebra

/-! Explicit expected propositions for the full-grid product algebra. -/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical

open ReyZygmund.MathlibOnly (CubeGrid)

namespace ReyZygmundVerification

open ReyZygmund.Geometry

def gridDifferenceMapSameContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (i : Fin m), 0 < d i →
    ∀ (D : CubeGrid (d i)) (a b : ℤ) (L Q : Box (Fin (d i))),
      L ∈ D.cubesAtGeneration a → Q ∈ D.cubesAtGeneration b →
      differenceMap i L * differenceMap i Q =
        if L = Q then differenceMap i Q else 0

def gridProductDifferenceMapFullContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (D : ∀ i, CubeGrid (d i))
    (a b : Fin m → ℤ), (∀ i, 0 < d i) → ∀ (A : Finset (Fin m))
      (K L : ∀ i, Box (Fin (d i))),
      (∀ i ∈ A, K i ∈ (D i).cubesAtGeneration (a i)) →
      (∀ i, L i ∈ (D i).cubesAtGeneration (b i)) →
      productDifferenceMap A K * productDifferenceMap Finset.univ L =
        if ∀ i ∈ A, K i = L i then productDifferenceMap Finset.univ L else 0

def gridAverageDifferenceMapZeroContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (i : Fin m), 0 < d i →
    ∀ (D : CubeGrid (d i)) (a b : ℤ) (K L : Box (Fin (d i))),
      K ∈ D.cubesAtGeneration a → L ∈ D.cubesAtGeneration b → ¬ K < L →
      averageMap i K * differenceMap i L = 0

def gridAverageProductDifferenceZeroContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (B : Finset (Fin m)) (i : Fin m),
    i ∈ B → 0 < d i → ∀ (D : CubeGrid (d i)) (a b : ℤ)
      (K : Box (Fin (d i))) (L : ∀ i, Box (Fin (d i))),
      K ∈ D.cubesAtGeneration a → L i ∈ D.cubesAtGeneration b → ¬ K < L i →
      averageMap i K * productDifferenceMap B L = 0

def gridProductAverageFullDifferenceZeroContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (D : ∀ i, CubeGrid (d i))
    (a b : Fin m → ℤ) (A : Finset (Fin m)) (K L : ∀ i, Box (Fin (d i))),
      (∀ i ∈ A, K i ∈ (D i).cubesAtGeneration (a i)) →
      (∀ i, L i ∈ (D i).cubesAtGeneration (b i)) →
      (∃ i ∈ A, 0 < d i ∧ ¬ K i < L i) →
      productAverageMap A K * productDifferenceMap Finset.univ L = 0

def gridRawProductDifferenceSameContract : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ) (D : ∀ i, CubeGrid (d i))
    (a b : Fin m → ℤ), (∀ i, 0 < d i) →
    ∀ (L Q : ∀ i, Box (Fin (d i))),
      (∀ i, L i ∈ (D i).cubesAtGeneration (a i)) →
      (∀ i, Q i ∈ (D i).cubesAtGeneration (b i)) →
      ∀ (F : boundedMeasurableFunctions d),
      rawProductDifference L (rawProductDifference Q F.1) =
        if L = Q then rawProductDifference Q F.1 else 0

end ReyZygmundVerification
