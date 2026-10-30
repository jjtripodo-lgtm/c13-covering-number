import C13Global.Final
import C13Global.Statistics
import Lean
open Lean Elab Command
private def wantedModule (n : Name) : Bool :=
  [`C13Global, `C13Enumeration, `C13RawStarRecovery, `C13Covering, `C13, `C13Arc, `C13Raw].any fun p => p.isPrefixOf n
private def infoKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
run_cmd do
  let env ← getEnv
  let entries := env.constants.fold (init := #[]) fun acc n ci =>
    match env.getModuleIdxFor? n with
    | none => acc
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if wantedModule m then acc.push (n,m,ci) else acc
  let entries := entries.qsort fun a b => Name.quickLt a.1 b.1
  for (n,m,ci) in entries do
    let axs ← collectAxioms n
    let bad := axs.filter fun a => !([`propext, `Classical.choice, `Quot.sound].contains a)
    if !bad.isEmpty then throwError "Unapproved axioms for {n}: {bad}"
    if ci.isUnsafe then throwError "Unsafe declaration {n}"
    liftIO <| IO.println ("DECL " ++ (Json.mkObj [
      ("name",toJson n.toString),("module",toJson m.toString),
      ("kind",toJson (infoKind ci)),("unsafe",toJson ci.isUnsafe),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress)
  for m in env.header.moduleNames do
    if wantedModule m then liftIO <| IO.println ("MODULE " ++ m.toString)
#print axioms C13.Global.all_catalog_foursets
#print axioms C13.Global.exact30_after_published_results

#print axioms C13.Global.minimum_bound_from_published_classification
#print axioms C13.Global.exact30_after_published_classification
