import Lean
import Lean.Util.CollectAxioms

/-! # Declaration inspection

`#rz_verify theorem against proposition` compares the elaborated theorem type with
a separately reviewed proposition and reports its transitive axioms. The inspector
is checking code, not a proof dependency. The public scripts check source
identities and coverage; mathematical correspondence is reviewed separately.

-/

open Lean Elab Command Meta

namespace ReyZygmundVerification

syntax (name := verifyDeclaration) "#rz_verify " ident " against " ident : command

@[command_elab verifyDeclaration]
def elabVerifyDeclaration : CommandElab := fun stx => do
  let target := stx[1].getId
  let specification := stx[3].getId
  unless (← getEnv).contains target do
    throwError "RZ_MISSING_DECLARATION: {target}"
  let info ← getConstInfo target
  let spec ← getConstInfo specification
  unless (match info with | .thmInfo _ => true | _ => false) do
    throwError "RZ_TARGET_KIND: selected declaration is not a theorem: {target}"
  let some expected := (match spec with | .defnInfo d => some d.value | _ => none)
    | throwError "RZ_CONTRACT_KIND: expected a reviewed proposition definition"
  unless info.levelParams.isEmpty && spec.levelParams.isEmpty do
    throwError "RZ_UNIVERSE_SCOPE: polymorphic universe contracts need an explicit extension"
  let typeMatches ← liftTermElabM do
    unless ← isProp expected do
      throwError "RZ_CONTRACT_KIND: specification is not a proposition"
    withTransparency .all <| isDefEq info.type expected
  let axioms ← collectAxioms target
  let env ← getEnv
  let origin := match env.getModuleIdxFor? target with
    | some idx => env.header.moduleNames[idx.toNat]!.toString
    | none => env.mainModule.toString
  let specOrigin := match env.getModuleIdxFor? specification with
    | some idx => env.header.moduleNames[idx.toNat]!.toString
    | none => env.mainModule.toString
  let rendered ← liftTermElabM <| withOptions (fun o => o.setBool `pp.all true) do
    return (← ppExpr info.type).pretty
  let report := Json.mkObj [
    ("target", toJson target.toString),
    ("contract", toJson specification.toString),
    ("module", toJson origin),
    ("contract_module", toJson specOrigin),
    ("matches", toJson typeMatches),
    ("type", toJson rendered),
    ("type_expression", toJson (reprStr info.type)),
    ("contract_expression", toJson (reprStr expected)),
    ("axioms", toJson (axioms.map Name.toString))]
  liftIO <| IO.println ("RZ_REPORT " ++ report.compress)

end ReyZygmundVerification
