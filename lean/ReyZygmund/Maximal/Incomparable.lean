import ReyZygmund.Maximal.WeakerGlobal

/-! # Maximal estimates for incomparable families

An incomparable family is weakly incomparable: containment makes the rectangles
identical, so every coordinate factor agrees. The finite and global estimates
therefore follow with the same constants. The general-input and global bounds
hold for every real exponent `p > 1`.
-/

open BoxIntegral MeasureTheory
open scoped BigOperators Classical ENNReal

open ReyZygmund.MathlibOnly (CubeGrid gridRectangles)

namespace ReyZygmund

open Geometry Projection

variable {m : ℕ} {d : Fin m → ℕ}

/-- The finite maximal estimate for product descendants, with strictly positive finite
input and the full stated range of real exponents.
-/
theorem finite_incomparable_maximal_norm
    (hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfpos : ∀ x ∈ productRectangle I, 0 < f x)
    (p : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 : ℝ) / 2) :
    Real.rpow (∫ x in productRectangle I,
      Real.rpow (finiteFamilyMaximal G (finiteInput I N f hf) x) p) (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productRectangle I, Real.rpow (f x) p) (1 / p) := by
  apply finite_weakly_incomparable_maximal_norm hm I N hd G hG ?_ f hf hfpos p hp hp3
  apply (weaklyIncomparable_iff_equal_factor (G : Set (∀ i, Box (Fin (d i))))).mpr
  intro R hR S hS hRS
  exact ⟨⟨0, by omega⟩, congrFun (hinc R hR S hS hRS) _⟩

/-- The finite estimate for nonnegative input. -/
theorem finite_incomparable_maximal_norm_nonneg
    (hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (f : ProductPoint d → ℝ) (hf : ProductLeafConstant I N f)
    (hfnonneg : ∀ x ∈ productRectangle I, 0 ≤ f x)
    (p : ℝ) (hp : 1 < p) (hp3 : p ≤ (3 : ℝ) / 2) :
    Real.rpow (∫ x in productRectangle I,
      Real.rpow (finiteFamilyMaximal G (finiteInput I N f hf) x) p) (1 / p) ≤
      maximalDimensionConstant d * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productRectangle I, Real.rpow (f x) p) (1 / p) := by
  apply finite_weaker_maximal_norm_nonneg hm I N hd G hG ?_ f hf hfnonneg p hp hp3
  intro R hR S hS hRS
  exact ⟨⟨0, by omega⟩, congrFun (hinc R hR S hS hRS) _⟩

/-- The finite incomparable estimate assumes integrability of the input and its
absolute p-th power on the top rectangle. The dimension-only factor is uniform in
the smallest scale, top rectangle, family, input and real exponent p > 1. -/
theorem finite_incomparable_general_input_norm
    (hm : 2 ≤ m)
    (I : ∀ i, Box (Fin (d i))) (N : Fin m → ℕ) (hd : ∀ i, 0 < d i)
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : G ⊆ productDescendants I N)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : IntegrableOn f (productRectangle I) volume)
    (hpow : IntegrableOn (fun x => Real.rpow |f x| p) (productRectangle I) volume) :
    Real.rpow (∫ x in productRectangle I,
      Real.rpow (finiteFunctionMaximal G f x) p) (1 / p) ≤
      (maximalDimensionConstant d + 3) * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x in productRectangle I, Real.rpow |f x| p) (1 / p) := by
  apply finite_weaker_general_input_norm hm I N hd G hG ?_ f p hp hf hpow
  intro R hR S hS hRS
  exact ⟨⟨0, by omega⟩, congrFun (hinc R hR S hS hRS) _⟩

/-- Global p-th power bound for a finite incomparable family of grid
rectangles and an Lp input. -/
theorem finite_grid_maximal_integral
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, CubeGrid (d i))
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : ↑G ⊆ gridRectangles D)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    (∫ x, Real.rpow (finiteFunctionMaximal G f x) p) ≤
      Real.rpow ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1)) p *
          ∫ x, Real.rpow |f x| p := by
  apply finite_weaker_grid_maximal_integral hm hd D G hG ?_ f p hp hf
  intro R hR S hS hRS
  exact ⟨⟨0, by omega⟩, congrFun (hinc R hR S hS hRS) _⟩

/-- Taking the real p-th root leaves exactly the announced norm constant. -/
theorem finite_grid_maximal_norm
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, CubeGrid (d i))
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : ↑G ⊆ gridRectangles D)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    Real.rpow (∫ x, Real.rpow (finiteFunctionMaximal G f x) p) (1 / p) ≤
      (maximalDimensionConstant d + 3) * (p / (p - 1)) ^ (m - 1) *
        Real.rpow (∫ x, Real.rpow |f x| p) (1 / p) := by
  apply finite_weaker_grid_maximal_norm hm hd D G hG ?_ f p hp hf
  intro R hR S hS hRS
  exact ⟨⟨0, by omega⟩, congrFun (hinc R hR S hS hRS) _⟩

/-- The finite power-integral estimate with nonnegative extended-real values. -/
theorem finite_grid_maximal_lintegral
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, CubeGrid (d i))
    (G : Finset (∀ i, Box (Fin (d i)))) (hG : ↑G ⊆ gridRectangles D)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    (∫⁻ x, (ENNReal.ofReal (finiteFunctionMaximal G f x)) ^ p) ≤
      (ENNReal.ofReal ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1))) ^ p *
          ∫⁻ x, (ENNReal.ofReal |f x|) ^ p := by
  apply finite_weaker_grid_maximal_lintegral hm hd D G hG ?_ f p hp hf
  intro R hR S hS hRS
  exact ⟨⟨0, by omega⟩, congrFun (hinc R hR S hS hRS) _⟩

/-- The countable supremum satisfies the uniform power-integral estimate. -/
theorem grid_family_maximal_lintegral
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, CubeGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    (∫⁻ x, (familyMaximal G f x) ^ p) ≤
      (ENNReal.ofReal ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1))) ^ p *
          ∫⁻ x, (ENNReal.ofReal |f x|) ^ p := by
  apply weaker_grid_family_maximal_lintegral hm hd D G hG ?_ f p hp hf
  intro R hR S hS hRS
  exact ⟨⟨0, by omega⟩, congrFun (hinc R hR S hS hRS) _⟩

/-- The global maximal function is finite almost everywhere. -/
theorem grid_family_maximal_ae_finite
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, CubeGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∀ᵐ x ∂volume, familyMaximal G f x < ∞ := by
  apply weaker_grid_family_maximal_ae_finite hm hd D G hG ?_ f p hp hf
  intro R hR S hS hRS
  exact ⟨⟨0, by omega⟩, congrFun (hinc R hR S hS hRS) _⟩

/-- Ordinary Lp form for the almost-everywhere finite representative, with
the exact `(p')^(m-1)` factor outside the norm. -/
theorem grid_family_maximal_eLpNorm
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, CubeGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, (∀ i, R i ≤ S i) → R = S)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (fun x => (familyMaximal G f x).toReal) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1)) * eLpNorm f (ENNReal.ofReal p) volume := by
  apply weaker_grid_family_maximal_eLpNorm hm hd D G hG ?_ f p hp hf
  intro R hR S hS hRS
  exact ⟨⟨0, by omega⟩, congrFun (hinc R hR S hS hRS) _⟩

/-- Incomparability is defined by inclusion of the product sets; its coordinatewise
formulation is equivalent. -/
theorem incomparable_grid_maximal_eLpNorm
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, CubeGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, productRectangle R ⊆ productRectangle S → R = S)
    (f : ProductPoint d → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (fun x => (familyMaximal G f x).toReal) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1)) * eLpNorm f (ENNReal.ofReal p) volume := by
  apply weaker_containment_grid_maximal_eLpNorm hm hd D G hG ?_ f p hp hf
  intro R hR S hS hRS
  exact ⟨⟨0, by omega⟩, congrFun (hinc R hR S hS hRS) _⟩

/-- Almost-everywhere finiteness of the Euclidean supremum. -/
theorem euclidean_grid_maximal_ae_finite
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, CubeGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, productRectangle R ⊆ productRectangle S → R = S)
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∀ᵐ x ∂volume, euclideanFamilyMaximal G f x < ∞ := by
  apply euclidean_weaker_grid_maximal_ae_finite hm hd D G hG ?_ f p hp hf
  intro R hR S hS hRS
  exact ⟨⟨0, by omega⟩, congrFun (hinc R hR S hS hRS) _⟩

/-- The main norm estimate in ordinary Euclidean coordinates, with the same
dimension-only constant. -/
theorem euclidean_grid_maximal_eLpNorm
    (hm : 2 ≤ m) (hd : ∀ i, 0 < d i) (D : ∀ i, CubeGrid (d i))
    (G : Set (∀ i, Box (Fin (d i)))) (hG : G ⊆ gridRectangles D)
    (hinc : ∀ R ∈ G, ∀ S ∈ G, productRectangle R ⊆ productRectangle S → R = S)
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (fun x => (euclideanFamilyMaximal G f x).toReal) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((maximalDimensionConstant d + 3) *
        (p / (p - 1)) ^ (m - 1)) * eLpNorm f (ENNReal.ofReal p) volume := by
  apply euclidean_weaker_grid_maximal_eLpNorm hm hd D G hG ?_ f p hp hf
  intro R hR S hS hRS
  exact ⟨⟨0, by omega⟩, congrFun (hinc R hR S hS hRS) _⟩

end ReyZygmund
