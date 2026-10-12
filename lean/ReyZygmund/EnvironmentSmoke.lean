import Mathlib

/-!
Installation smoke test: import Mathlib and check an elementary real-number theorem.
-/

namespace ReyZygmund.EnvironmentSmoke

theorem square_nonneg (x : ℝ) : 0 ≤ x ^ 2 := sq_nonneg x

end ReyZygmund.EnvironmentSmoke
