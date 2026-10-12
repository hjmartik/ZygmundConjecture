/-! Deliberately untrusted axiom through a helper; never a production dependency. -/
namespace VerificationFixtures

axiom extraAssumption : False
theorem axiomHelper : False := extraAssumption

end VerificationFixtures
