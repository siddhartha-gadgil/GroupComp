import Mathlib
/-!
# Examples of Proofs

We see our next proofs, most of which involve the `≤` relation on natural numbers. 

We will see that the natural numbers are "defined" in terms of the `zero` and `succ` constructors.

* `Nat.zero : ℕ` 
* `Nat.succ : ℕ → ℕ`

Analogous to this, (modulo renaming) the `≤` relation is defined in terms of the `le_refl` and `le_step` constructors.

* `Nat.le : ℕ → ℕ → Prop`
* `Nat.le_refl : ∀ n : ℕ, n ≤ n`
* `Nat.le_step : ∀ {n m : ℕ}, n ≤ m → n ≤ Nat.succ m`
-/

#check (10.5 : ℝ)
#eval ((22 : ℚ)/6 : ℚ) 
#eval 10.5

#check Nat -- Type
#check Nat.zero -- ℕ 
#check Nat.succ -- ℕ → ℕ 

#check Nat.le -- ℕ → ℕ → Prop 
#check Nat.le_step -- ∀ {n m : ℕ}, n ≤ m → n ≤ Nat.succ m
#check Nat.le_refl -- ∀ n : ℕ, n ≤ n

theorem three_le_self : 3 ≤ 3 := Nat.le_refl 3

example : 5 ≤ 5 := Nat.le_refl _ 

theorem three_le_four : 3 ≤ 4 :=
  Nat.le_step (Nat.le_refl _)

example : 7 ≤ 9 :=
  Nat.le_step 
    (Nat.le_step (Nat.le_refl 7))

example : 10 ≤ 12 := by
  apply Nat.le_step
  apply Nat.le_step
  apply Nat.le_refl

example : 10 ≤ 102 := by
  repeat (
    first | apply Nat.le_refl | 
      apply Nat.le_step
    )

example : 12 ≤ 2023 := by decide
