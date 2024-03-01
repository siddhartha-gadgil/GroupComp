import Mathlib

/-!
# Recursive functions

We have defined functions in terms of other functions. Besides this essentially the only way to define functions is _recursion_. In __Dependent Type Theory__ recursion/induction is very powerful.

In particular, unlike imperative programming all loops are implemented in terms of recursion.

The first example is the factorial function:
-/

/-- The factorial function -/
def fctrl(n : ℕ):  ℕ :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * (fctrl n)

/-!
We check by evaluating this

#eval fctrl 5 -- 120
-/
#eval fctrl 5 -- 120

/-!
## Fibonacci numbers:

These are given by the recursive definition

* `fib 0 = 1`
* `fib 1 = 1`
* `fib (n + 2) = fib n + (fib (n + 1))`
-/
def fib : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 => fib n + (fib (n + 1))

/-!
The above definition is not efficient as a single computation is called many times.

We can instead define pairs, so
if  `(a, b) = (fib n, fib (n + 1))`
then `(fib (n + 1), fib (n + 2)) = (b, a+ b)`

To define Fibonacci pairs as above, we have two choices. We can view the pair at `n` as obtained by `n` iterations of the function `g: (a, b) ↦ (b, a + b)` starting with the pair `(1,1)`. Note that we can recursively use either `g^(n + 1) = g^n ∘ g` or `g^(n + 1) = g ∘ g^n`. The former is more efficient as it means the recursive function is called at the end to give a result, with modified arguments. This allows so called _tail call optimization_, where new copies of the function are not created.
-/
def fibAux (a b n : ℕ) : ℕ × ℕ  :=
  match n with
  | 0 => (a, b)
  | k + 1 => fibAux b (a + b) k

def fib'(n) := (fibAux 1 1 n).1

#eval fib' 42

/-!
The following definition is clearly wrong and will loop infinitely. Indeed if we attempt to define

```lean
def silly_fib : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 => silly_fib n + (silly_fib (n + 3))
```

we get the error message

```lean
fail to show termination for
  silly_fib
with errors
argument #1 was not used for structural recursion
  failed to eliminate recursive application
    silly_fib (n + 3)

structural recursion cannot be used

failed to prove termination, use `termination_by` to specify a well-founded relation
```
-/
partial def silly_fib : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 => silly_fib n + (silly_fib (n + 3))

#check silly_fib -- ℕ → ℕ

/-!
However even if functions terminate we can still get such an error. This is because Lean does not know that the function is terminating. We can fix this by adding the `partial` keyword but better still we can prove termination.

Thus, the following definition is correct but gives an error.
```lean
def hcf (a b : ℕ) : ℕ :=
  if b < a then hcf b a
  else
    if a = 0 then b
    else hcf a (b - a)

#eval hcf 18 12 -- 6
```
-/

#check Nat.mod_lt

def hcf (a b : ℕ) : ℕ :=
  if b < a then hcf b a
  else
    if c':a = 0 then b
  else
    have : b % a < a := by
      apply Nat.mod_lt
      apply Nat.pos_of_ne_zero
      assumption
    hcf (b % a) a
termination_by a b => a

#eval hcf 8 12 -- 4

#check Empty


/-!
Lean has to allow partial definitions due to deep results of Church-Gödel-Turing-..., which say for example that we cannot prove that a Lean interpreter in Lean terminates.
-/

def sumUpto : ℕ → ℕ
| 0 => 0
| n + 1 => n + 1 + sumUpto n

theorem sum_formula (n: ℕ) :  sumUpto n = (n * (n + 1) : ℚ) / 2  := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [sumUpto, ih]
    linarith

def sumAux (n: ℕ)(accum : ℕ) : ℕ :=
  match n with
  | 0 => accum
  | n + 1 => sumAux n (accum + (n + 1))

#eval sumAux 3 1

  -- partial def wrong(n: ℕ): Empty :=
--   wrong (n + 1)

axiom wrong : ℕ → Empty

theorem vac_contra : ∀ e : Empty, ∀ n: ℕ,
  wrong n = e →  n = 2 := by
  intro e
  induction e

theorem one_eq_two : 1 = 2 := by
  let e := wrong 1
  let h := vac_contra e 1
  apply h
  rfl

/-!
```lean
partial def wrong(n: ℕ): Empty :=
  wrong (n + 1)
```

gives the error message
```lean
failed to compile partial definition 'wrong', failed to show that type is inhabited and non empty
```
-/
