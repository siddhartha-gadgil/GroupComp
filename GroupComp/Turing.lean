import Lean
open Lean Meta Elab Term

/-- Returns expression for a term different from given one -/
def flipExpr (e: Expr) : TermElabM Expr := do
  let zeroExpr ← mkConst ``Nat.zero
  if ←isDefEq e zeroExpr then 
    mkAppM ``Nat.succ #[zeroExpr]
  else
    return zeroExpr

/-- Tries to parse `s` and run on the string `s`
* On success, expression returns a different term 
* on failure, returns (expression for) `0`

It follows that `evil (evil) ≠ evil (evil)` after unwrapping.
--/
def evil (s: String)(env: Environment) : TermElabM Expr :=
  try
    let stx? := Parser.runParserCategory env `term s |>.toOption
    let code := Expr.lit <| Literal.strVal s
    match   stx? with
    | some program => 
      let fn ← elabTerm program none
      flipExpr <| ← reduce  <| mkApp fn code
    | none => 
      mkConst ``Nat.zero 
  catch _ =>
    Term.mkConst ``Nat.zero 

elab "see_evil" s:str : term => do
  evil s.getString (← getEnv)

def egFn: String → Nat := fun _ => 0

#eval see_evil "egFn" -- 1

def constNat (n: Nat) (_: String) : Nat := n

#eval see_evil "constNat 0" -- 1

#eval see_evil "constNat 2" -- 0

#eval see_evil "3" -- 0

-- #eval see_evil "evil"
