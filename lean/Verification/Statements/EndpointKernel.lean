import ReyZygmund.Maximal.EndpointKernel

/-! Expected scalar endpoint-kernel propositions. -/

open MeasureTheory Set
open scoped ENNReal

namespace ReyZygmundVerification

def endpointLogExpKernelContract : Prop :=
  ∀ (k : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
    (∫⁻ t : ℝ in Ioi 0,
      ENNReal.ofReal (Real.exp (-ε * t) * (Real.log (Real.exp 1 + Real.exp t)) ^ k)) ≤
      ENNReal.ofReal (Real.exp 2 * (k.factorial : ℝ) / ε ^ (k + 1))

def endpointTruncatedLogKernelContract : Prop :=
  ∀ (k : ℕ) (p a : ℝ), 1 < p → p ≤ 2 → 0 ≤ a →
    (∫⁻ t : ℝ in Ioo 0 (2 * a),
      ENNReal.ofReal (Real.rpow t (p - 2) *
        (Real.log (Real.exp 1 + 2 * a / t)) ^ k)) ≤
      ENNReal.ofReal (Real.rpow (2 * a) (p - 1) * Real.exp 2 *
        (k.factorial : ℝ) / (p - 1) ^ (k + 1))

end ReyZygmundVerification
