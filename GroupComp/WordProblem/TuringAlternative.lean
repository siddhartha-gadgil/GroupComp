import Lean
open Lean Meta Elab Term

unsafe def evil (nm : Name) : TermElabM Name := do
  let .ok f := (← getEnv).evalConst (Name → TermElabM Name) .empty nm |   
    throwError "The input must have type `Name → TermElabM Name`."
  f nm

def testFn (nm : Name) : TermElabM Name := return .str nm "xyz"

#eval evil `testFn

-- #eval evil `evil