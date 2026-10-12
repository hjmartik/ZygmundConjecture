/-! Propositions for adversarial verifier fixtures, not paper claims. -/
namespace VerificationFixtures

def addZeroContract : Prop := ∀ n : Nat, n + 0 = n
def falseContract : Prop := False
def trueContract : Prop := True

end VerificationFixtures
