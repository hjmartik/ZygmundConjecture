import ReyZygmund.Geometry.Rounding

open ReyZygmund.MathlibOnly (rounding)

namespace ReyZygmundVerification

open ReyZygmund.Geometry

def roundedScaleBinsContract : Prop :=
  ∀ {s : ℝ}, 0 < s → ∀ k : ℤ,
    rounding s = k ↔ (2 : ℝ) ^ (k - 3) < s ∧ s ≤ (2 : ℝ) ^ (k - 2)

def roundedScaleBoundsContract : Prop :=
  ∀ {s : ℝ}, 0 < s →
    4 * s ≤ (2 : ℝ) ^ rounding s ∧ (2 : ℝ) ^ rounding s < 8 * s

def roundedScaleMonotonicityContract : Prop :=
  ∀ {s t : ℝ}, 0 < s → s ≤ t → rounding s ≤ rounding t

def roundedScaleStrictOrderContract : Prop :=
  ∀ {s t : ℝ}, 0 < t → rounding s < rounding t → s < t

end ReyZygmundVerification
