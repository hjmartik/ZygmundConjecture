import Lean
import Lean.Util.FoldConsts

/-!
# Inspect the declarations used by a proof

This audit command follows checked types, proof bodies, and separately labeled
inductive structure. The caller supplies the exact project module boundary.
External constants are reported as boundary edges; their bodies are not expanded.
The graph records syntactic dependencies, not mathematical proof correspondence.
-/

open Lean Elab Command

namespace ReyZygmundVerification

private def declarationModule (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

private def structuralDependencies (info : ConstantInfo) : Array Name :=
  match info with
  | .inductInfo v => (v.all ++ v.ctors).toArray
  | .ctorInfo v => #[v.induct]
  | .recInfo v => v.rules.foldl
      (fun names rule => names ++ #[rule.ctor] ++ rule.rhs.getUsedConstants) v.all.toArray
  | _ => #[]

syntax "#rz_dependencies" "modules" ident,+ "targets" ident,+ : command

elab_rules : command
  | `(#rz_dependencies modules $moduleIds:ident,* targets $roots:ident,*) => do
    let env := (← getEnv).setExporting false
    let kernel := env.checked.get
    let moduleNames := moduleIds.getElems.map (·.getId)
    let rootNames := roots.getElems.map (·.getId)
    let internal := fun name => moduleNames.contains (declarationModule env name)
    let mut uniqueRoots : NameSet := {}
    for name in rootNames do
      if uniqueRoots.contains name then
        throwError "RZ_DUPLICATE_ROOT: {name}"
      uniqueRoots := uniqueRoots.insert name
      match kernel.find? name with
      | some (.thmInfo _) => pure ()
      | some _ => throwError "RZ_ROOT_KIND: {name}"
      | none => throwError "RZ_MISSING_ROOT: {name}"
      unless internal name do
        throwError "RZ_ROOT_BOUNDARY: {name}"
    let mut todo := rootNames
    let mut seen : NameSet := {}
    let mut rows : Array Json := #[]
    while !todo.isEmpty do
      let name := todo.back!
      todo := todo.pop
      if !seen.contains name then
        seen := seen.insert name
        let some info := kernel.find? name | throwError "RZ_MISSING_DEPENDENCY: {name}"
        let typeDeps := info.type.getUsedConstants
        let bodyDeps := match info.value? (allowOpaque := true) with
          | some value => value.getUsedConstants
          | none => #[]
        let structuralDeps := structuralDependencies info
        todo := todo ++ (typeDeps ++ bodyDeps ++ structuralDeps).filter internal
        let kind := match info with
          | .thmInfo _ => "theorem"
          | .defnInfo _ => "definition"
          | .axiomInfo _ => "axiom"
          | .opaqueInfo _ => "opaque"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
          | _ => "other"
        rows := rows.push (Json.mkObj [
          ("name", toJson name.toString),
          ("module", toJson (declarationModule env name).toString),
          ("kind", toJson kind),
          ("type_dependencies", toJson (typeDeps.map Name.toString)),
          ("body_dependencies", toJson (bodyDeps.map Name.toString)),
          ("structural_dependencies", toJson (structuralDeps.map Name.toString))])
    liftIO <| IO.println ("RZ_DEPENDENCIES " ++ (Json.mkObj [
      ("roots", toJson (rootNames.map Name.toString)),
      ("modules", toJson (moduleNames.map Name.toString)),
      ("scope", toJson "Syntactic references in checked declarations; external bodies are not expanded"),
      ("declarations", toJson rows)]).compress)

end ReyZygmundVerification
