import Lean
open Lean Meta Elab Term

/-- natural number from expression built from `Nat.zero` and `Nat.succ` -/
partial def exprNatM : TermElabM Expr → TermElabM Nat := fun exprM => 
  do
    let expr ← exprM 
    let mvar ←  mkFreshExprMVar (some (mkConst ``Nat))
    let sExp := mkApp (mkConst ``Nat.succ) mvar
    if ← isDefEq sExp expr then
      Term.synthesizeSyntheticMVarsNoPostponing
      let prev ← exprNatM (whnf mvar)
      return Nat.succ prev
    else 
    if ← isDefEq (mkConst `Nat.zero) expr then
      return Nat.zero
    else
      throwError m!"{expr} not a Nat expression"

def elabSucc(n: TermElabM Nat) : TermElabM Nat := do
  return (Nat.succ (←n))

def evil (s: String)(env: Environment) : TermElabM Expr :=
  try
    let stx? := Parser.runParserCategory env `term s |>.toOption
    let t := stx?.getD (← `(Nat.zero))
    let code := Expr.lit <| Literal.strVal s
    let e ← elabTerm t none
    let e' := mkApp e code
    let e' ← reduce e' 
    reduce <| ← mkAppM ``elabSucc #[e'] 
  catch _ =>
    return Lean.mkConst ``Nat.zero 

def runEvil(s: String) : TermElabM Expr := do
  let env ← getEnv
  evil s env

#eval runEvil "2"

def egFn: String → TermElabM Nat := fun s => return 3 + s.length

#eval runEvil "egFn" -- 4 (= egFn ("egFn") + 1)

-- #eval runEvil "evil"
