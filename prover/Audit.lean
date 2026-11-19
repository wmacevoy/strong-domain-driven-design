import Lean
open Lean

/-! The audit. `lean --run Audit.lean C`, with the compiled files on LEAN_PATH.

CClaims.lean is written by a person or an agent, and is trusted for nothing. This asks of its
compiled form, without reading its text or running anything it says:

  1. `C.Claims.owed` is there, and is a proof of `C.Owed`, the statement in COwed.lean, which was
     generated from the C++ and compiled before the claims were looked at;
  2. everything it rests on, followed to the end, uses no axiom but the three below. So no `sorry`,
     no axiom of the claims' own, and no trust in compiled code (`native_decide`, `bv_decide`),
     which a claims file could have swapped for code of its own.

It does not check the proof: prove.sh has Lean's kernel do that again, with `leanchecker`. -/

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Every constant `c` rests on, into `seen`; and the axioms among them, into `found`. -/
partial def rests (env : Environment) (c : Name) : StateM (NameSet × NameSet) Unit := do
  if (← get).1.contains c then return
  modify fun (seen, found) => (seen.insert c, found)
  let uses (e : Expr) : StateM (NameSet × NameSet) Unit := e.getUsedConstants.forM (rests env)
  match env.find? c with
  | some (.axiomInfo v) => modify (fun (seen, found) => (seen, found.insert c)); uses v.type
  | some (.defnInfo v) => uses v.type; uses v.value
  | some (.thmInfo v) => uses v.type; uses v.value
  | some (.opaqueInfo v) => uses v.type; uses v.value
  | some (.ctorInfo v) => uses v.type
  | some (.recInfo v) => uses v.type
  | some (.inductInfo v) => uses v.type; v.ctors.forM (rests env)
  | some (.quotInfo _) => pure ()
  | none => pure ()

unsafe def main (args : List String) : IO UInt32 := do
  let [c] := args | do IO.eprintln "usage: lean --run Audit.lean CLASS"; return 2
  initSearchPath (← findSysroot)
  let claims := (c ++ "Claims").toName
  let owedModule := (c ++ "Owed").toName
  let proof := c.toName ++ `Claims ++ `owed
  let owed := c.toName ++ `Owed
  withImportModules #[{ module := owedModule }, { module := claims }] {} fun env => do
    let refuse (why : String) : IO UInt32 := do IO.println s!"REFUSED: {why}"; return 1
    let some info := env.find? proof | refuse s!"the claims do not have `{proof}`"
    if info.type != mkConst owed then
      return ← refuse s!"`{proof}` is not a proof of `{owed}`: it is of {info.type}"
    let from? := (env.getModuleIdxFor? owed).bind fun i => env.header.moduleNames[i.toNat]?
    if from? != some owedModule then
      return ← refuse s!"`{owed}` is not the one in {owedModule}"
    unless info matches .thmInfo _ do
      return ← refuse s!"`{proof}` is not a theorem"
    let (_, (seen, found)) := (rests env proof).run ({}, {})
    let found := found.toList
    IO.println s!"{proof} : {owed}"
    IO.println s!"rests on {seen.size} definitions and theorems, and the axioms {found}"
    match found.filter (!allowed.contains ·) with
    | [] => return 0
    | bad => refuse s!"it rests on {bad}, which is not one of {allowed}"
