import ReyZygmund.Geometry.RootAverageLp

/-! Lp contraction for top-cube averages, with coefficient one. -/

open BoxIntegral MeasureTheory ReyZygmund.Geometry

namespace ReyZygmundVerification

def coordinateRootAverageLpContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d), ProductLeafConstant I N F.1 →
  ∀ (j : Fin m) (p : ℝ), 1 ≤ p →
    (∫ x in productBox I, Real.rpow |(averageMap j (I j) F).1 x| p) ≤
      ∫ x in productBox I, Real.rpow |F.1 x| p

def productRootAverageLpContract : Prop :=
  ∀ {m : ℕ} {d : Fin m → ℕ}
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ)
    (F : boundedMeasurableFunctions d), ProductLeafConstant I N F.1 →
  ∀ (A : Finset (Fin m)) (p : ℝ), 1 ≤ p →
    (∫ x in productBox I, Real.rpow |(productAverageMap A I F).1 x| p) ≤
      ∫ x in productBox I, Real.rpow |F.1 x| p

end ReyZygmundVerification
