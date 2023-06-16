import Mathlib
/-!
# Welcome to the course

We start with a quick tour, where we:

* Use Lean as a calculator
* Define some functions and call them.
* Look at some types.
* Look at some proofs.

We will then see
* A glimpse of AI.
* A detailed example with programs and proofs.
-/

    
example : 3 ≤ 7 := by 
  repeat (first | apply Nat.le_refl| apply Nat.le_step) 

macro "nat_le" : tactic => do
  `(tactic| repeat (first | apply Nat.le_refl| apply Nat.le_step))

example : 2 ≤ 8 := by nat_le

macro "step_with" step:term "finish_with" fin:term : tactic => do
  `(tactic| repeat (first | apply $fin| apply $step))

example : 2 ≤ 8 := by 
  step_with Nat.le_step finish_with Nat.le_refl 

example : 2 ≤ 8 := by 
  step_with Nat.succ_le_succ finish_with Nat.zero_le 

#eval [1, 2][0]

example (n : Nat) : (n :: [1, 2, 3])[1] = 1 := by 
  rfl

def hcf(a b : ℕ) : ℕ := 
  if c':a < b then hcf b a 
  else 
    if c:b = 0 then a 
    else
      have b_pos : b > 0 := by 
        apply Nat.pos_of_ne_zero
        assumption      
      have : (a - b) < a := by 
        apply Nat.sub_lt_of_pos_le b a b_pos
        apply Nat.le_of_not_lt 
        assumption
      hcf (a - b) b
termination_by _ a b => (b, a)

#check Nat.pos_of_ne_zero
#check Nat.sub_lt_of_pos_le

#eval List.range 10 |>.map fun n => hcf 100 n
/-!
## Lean as a calculator.

We begin by using Lean as a calculator. We can use `#eval` to evaluate expressions.

```lean
#eval 1 + 2 -- 3

#eval "Hello " ++ "world!" -- "Hello world!"
```
-/
#eval 1 + 2

#eval "Hello " ++ "world!"

/-- An arbitrary number. -/
def some_number := 42

/-!
We next evaluate an expression involving a definition.

```lean 
#eval some_number + 23 -- 65
```
-/

#eval some_number + 23

/-! 
## Defining functions

We next define some functions. These are defined in terms of previously defined functions.
-/
/-- Add `2` to a natural number -/
def add_two (n : ℕ) : ℕ := n + 2

/-- Cube a natural number -/
def cube (n : ℕ) : ℕ := n * n * n

/-!
```lean
#eval cube (add_two 3) -- 125
```
-/
#eval cube (add_two 3)

/-- Cube a natural number -/
def cube' := fun (n : ℕ) ↦ n * n * n

/-- Cube a natural number -/
def cube'' : ℕ → ℕ := fun n ↦ n * n * n

example := λ (n : ℕ) => n * n * n

/-! 
## Types 

Terms in Lean, including functions, have types, which can be seen using `#check` 

```lean
#check 1 + 2 -- ℕ

#check "Hello " ++ "world!" -- String

#check add_two -- ℕ → ℕ
#check cube   -- ℕ → ℕ

#check ℕ -- Type
#check Type -- Type 1
#check ℕ → ℕ -- Type
```
-/

#check 1 + 2

#check "Hello " ++ "world!"

#check add_two
#check cube 

#check ℕ
#check Type 
#check ℕ → ℕ

/-!
We next define a function of two arguments, and look at its type. We see that this is defined as a function from `ℕ` to a function from `ℕ` to `ℕ`.

-/
/-- Sum of squares of natural numbers `x` and `y` -/
def sum_of_squares (x y : ℕ) : ℕ := x * x + y * y

/-!
```lean
#check sum_of_squares -- ℕ → ℕ → ℕ

#check sum_of_squares 3 -- ℕ → ℕ
```

We can also define this in a way that makes the type clearer.
-/

#check sum_of_squares -- ℕ → (ℕ → ℕ)

#check sum_of_squares 3 -- ℕ → ℕ

/-- Sum of squares of natural numbers `x` and `y` -/
def sum_of_squares' : ℕ → ℕ → ℕ := 
  fun x ↦ fun y ↦  x * x + y * y
