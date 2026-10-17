import ReyZygmund.Continuous.DyadicExtension

/-! Explicit propositions for the paper's dyadic side-function extension. -/

open BoxIntegral
open ReyZygmund ReyZygmund.Geometry ReyZygmund.Continuous
open scoped BigOperators Classical

open ReyZygmund.MathlibOnly (CubeGrid zygmundRectangles dyadicZygmundRectangles)

namespace ReyZygmundVerification

def dyadicExtensionMonotoneContract : Prop :=
  ∀ {n : ℕ} (Phi : (Fin n → ℤ) → ℤ), Monotone Phi →
    Monotone (dyadicPhiExtension Phi)

def dyadicExtensionRecoveryContract : Prop :=
  ∀ {n : ℕ} (Phi : (Fin n → ℤ) → ℤ) (k : Fin n → ℤ),
    (dyadicPhiExtension Phi
      (fun j => ⟨(2 : ℝ) ^ k j, zpow_pos (by norm_num : (0 : ℝ) < 2) _⟩)).1 =
        (2 : ℝ) ^ Phi k

def dyadicContinuousInclusionContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (D : ∀ i, CubeGrid (d i)) (Phi : (Fin n → ℤ) → ℤ),
    dyadicZygmundRectangles D Phi ⊆ zygmundRectangles d (dyadicPhiExtension Phi)

def dyadicContinuousMaximalContract : Prop :=
  ∀ {n : ℕ} {d : Fin (n + 1) → ℕ}
    (D : ∀ i, CubeGrid (d i)) (Phi : (Fin n → ℤ) → ℤ)
    (f : (Fin (∑ i, d i) → ℝ) → ℝ) (x : Fin (∑ i, d i) → ℝ),
    euclideanFamilyMaximal (dyadicZygmundRectangles D Phi) f x ≤
      euclideanFamilyMaximal (zygmundRectangles d (dyadicPhiExtension Phi)) f x

end ReyZygmundVerification
