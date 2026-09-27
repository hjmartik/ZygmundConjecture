import ReyZygmund.Maximal.GlobalSquare
import Verification.Challenges.Square

/-! # The signed maximal–square-function estimate

For a function equal almost everywhere to a finite sum of product martingale
differences, the full-grid signed maximal function is bounded in `L^p` by its
square function, with a dimensional constant, for `1 ≤ p ≤ 3/2`. The supremum ranges
over the entire grid. The averages, differences and square sum agree with their
independently stated formulas. -/

open BoxIntegral MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ReyZygmund.Main

open Geometry

theorem square_raw_difference_eq {m : ℕ} {d : Fin m → ℕ}
    (Q : ∀ i, Box (Fin (d i))) (g : ProductPoint d → ℝ) :
    ReyZygmundVerification.Challenges.squareRawDifference Q g =
      rawProductDifference Q g := rfl

theorem square_signed_maximal_eq {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, DyadicGrid (d i)) (g : ProductPoint d → ℝ) :
    ReyZygmundVerification.Challenges.squareSignedMaximal D g =
      signedGridMaximal D g := rfl

theorem square_function_eq {m : ℕ} {d : Fin m → ℕ}
    (D : ∀ i, DyadicGrid (d i)) (g : ProductPoint d → ℝ) :
    ReyZygmundVerification.Challenges.squareFunction D g = fullGridSquare D g := rfl

/-- The paper's square-function estimate, including one parameter and p = 1. -/
theorem product_square_theorem :
    ReyZygmundVerification.Challenges.productSquareStatement := by
  intro m d _hm hd D H hH g hex p hp hp3
  simp only [square_raw_difference_eq] at hex
  simp only [square_signed_maximal_eq, square_function_eq]
  exact full_grid_square_estimate D hd H hH g hex p hp hp3

end ReyZygmund.Main
