import ReyZygmund.Geometry.ScalarCover

namespace ReyZygmundVerification

def scalarShiftedCoverContract : Prop :=
  ∀ L s u sigma : ℝ, 0 < L → 0 < s → 3 * s < L →
    (sigma = 1 ∨ sigma = -1) →
    ∃ a : Fin 3, ∃ z : ℤ,
      L * ((z : ℝ) + sigma * (a.val : ℝ) / 3) < u ∧
      u + s < L * ((z : ℝ) + sigma * (a.val : ℝ) / 3 + 1)

end ReyZygmundVerification
