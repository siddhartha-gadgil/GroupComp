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
-/


/-! 
## Defining functions

We next define some functions. These are defined in terms of previously defined functions.
-/

/-! 
## Types 

Terms in Lean, including functions, have types, which can be seen using `#check` 
```
-/

/-!
We next define a function of two arguments, and look at its type. We see that this is defined as a function from `ℕ` to a function from `ℕ` to `ℕ`.

We can also define this in a way that makes the type clearer.
-/

/-!
## Proofs

We look at a couple of simple proofs. This also illustrates implicit parameters.
-/
