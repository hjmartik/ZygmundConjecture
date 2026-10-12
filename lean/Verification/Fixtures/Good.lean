/-! A theorem with empty axiom closure, used only by the verifier tests. -/
namespace VerificationFixtures

theorem addZero (n : Nat) : n + 0 = n := rfl

end VerificationFixtures
