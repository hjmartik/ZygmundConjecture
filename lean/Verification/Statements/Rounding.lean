import ReyZygmund.Geometry.Rounding

namespace ReyZygmundVerification

open ReyZygmund.Geometry

def roundedScaleBinsContract : Prop :=
  ∀ {s : ℝ}, 0 < s → ∀ k : ℤ,
    roundedScale s = k ↔ (2 : ℝ) ^ (k - 3) < s ∧ s ≤ (2 : ℝ) ^ (k - 2)

def roundedScaleBoundsContract : Prop :=
  ∀ {s : ℝ}, 0 < s →
    4 * s ≤ (2 : ℝ) ^ roundedScale s ∧ (2 : ℝ) ^ roundedScale s < 8 * s

def roundedScaleMonotonicityContract : Prop :=
  ∀ {s t : ℝ}, 0 < s → s ≤ t → roundedScale s ≤ roundedScale t

def roundedScaleStrictOrderContract : Prop :=
  ∀ {s t : ℝ}, 0 < t → roundedScale s < roundedScale t → s < t

end ReyZygmundVerification
