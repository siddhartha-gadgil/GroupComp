import Lean
open Lean Meta Elab Term

/-- natural number from expression built from `Nat.zero` and `Nat.succ` -/
partial def exprNat : Expr → TermElabM Nat := fun expr => 
  do
    let mvar ←  mkFreshExprMVar (some (mkConst ``Nat))
    let sExp := mkApp (mkConst ``Nat.succ) mvar
    if ← isDefEq sExp expr then
      Term.synthesizeSyntheticMVarsNoPostponing
      let prev ← exprNat (← whnf mvar)
      return Nat.succ prev
    else 
    if ← isDefEq (mkConst `Nat.zero) expr then
      return Nat.zero
    else
      throwError m!"{expr} not a Nat expression"

def evil (s: String)(env: Environment) : TermElabM Nat :=
  try
    let stx? := Parser.runParserCategory env `term s |>.toOption
    let t := stx?.getD (← `(Nat.zero))
    let code := Expr.lit <| Literal.strVal s
    let e ← elabTerm t none
    let e' := mkApp e code
    let e' ← reduce e' 
    exprNat <| ← mkAppM ``Nat.succ #[e'] 
  catch _ =>
    return 0

def runEvil(s: String) : TermElabM Nat := do
  let env ← getEnv
  evil s env

#eval runEvil "2"

def egFn: String → Nat := fun s => 3 + s.length

#eval runEvil "egFn" -- 4 (= egFn ("egFn") + 1)

-- #eval runEvil "evil"
