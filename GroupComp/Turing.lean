import Lean
open Lean Meta Elab Term

/-!
# Turing's diagonal argument

We illustrate Turing's diagonal argument in Lean. This is why we need to allow `partial def`s in Lean.

The argument works so long as we have an *interpreter* function. This means we can encode lean programs as strings and run them on given string inputs. 

So in any self-interpreted language, we cannot decide whether a program halts on a given input.
-/

/-- Returns expression for a term different from given one -/
def flipExpr (e: Expr) : TermElabM Expr := do
  let zeroExpr ← mkConst ``Nat.zero
  if ←isDefEq e zeroExpr then 
    mkAppM ``Nat.succ #[zeroExpr]
  else
    return zeroExpr

/-- 
Tries to parse `s` and run on the string `s`. More precisely, `s` is parsed and elaborated to an expression `fn`.
Then, `fn` is applied to an expression for the string literal `s` and reduced. 

* On success, expression returns a different term: `1` if the term is`0`, `0` otherwise. 
* On failure, returns (expression for) `0`

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
