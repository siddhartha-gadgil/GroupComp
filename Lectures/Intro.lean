import Mathlib
/-!
# Welcome

We start with a quick tour, where we:

* Use Lean as a calculator
* Define some terms and functions and apply functions.
* Look at some types, including (curried) function types.
* Look at some proofs.

-/


/-!
## Lean as a calculator.

We begin by using Lean as a calculator. We can use `#eval` to evaluate expressions. We can also evaluate terms we have defined.

## Types

Terms in Lean, including functions, have types, which can be seen using `#check`


-/

#eval 2 + 3 * 5

def two := 2

def three : ℕ := 3

def four : Nat := 4

#eval three * four

#check four
#print four
#reduce (four * three)


/-!
## Defining functions

We next define some functions. These are defined in terms of previously defined functions.


-/

/-- The cube of a number -/
def cube (n : ℕ) := n * n * n

#check cube -- ℕ → ℕ
#print cube
#reduce cube

#eval cube 3 -- 27
#check cube 3 -- ℕ


def cube' : ℕ → ℕ := fun n : ℕ  ↦ n * n * n


/-!
We next define a function of two arguments, and look at its type. We see that this is defined as a function from `ℕ` to a function from `ℕ` to `ℕ`.

We can also define this in a way that makes the type clearer.
-/

def sumOfSquares (n : ℕ) (m : ℕ) :=
  n * n + m * m

#eval sumOfSquares 2 3

def sumOfCubes : ℕ → ℕ → ℕ  :=
  fun n ↦ fun m ↦ cube n + cube m

#eval sumOfCubes 3 4 -- 9

/-!
## Proofs

We look at a couple of simple proofs. This also illustrates implicit parameters.
-/

theorem one_plus_one : 1 + 1 = 2 := rfl

def one_plus_two : 1 + 2 = 3 := rfl

def cube'' : ℕ → ℕ := fun n ↦ n * n *n

-- #eval cube'' 3

#check rfl
#check Eq.refl

example : 3 = 2 + 1 := refl 3

example : 4 = 2 + 2 := refl _

example : 7 = 3 + 4 := @rfl ℕ 7

example : 7 = 3 + 4 := @rfl _ 7

def cube! (n : ℕ) : ℝ := n * n * n

#check cube!
