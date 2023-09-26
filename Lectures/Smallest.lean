import Mathlib

/-!
# Smallest in List: Algorithm with proofs

We illustrate the combination of algorithmic and proof parts in Lean with:

* An algorithm to find the smallest element in a non-empty list of elements of a linearly ordered type.
* A proof that the result of the algorithm is indeed the smallest element in the list.
-/

variable {α : Type}[LinearOrder α]

#check min_eq_right -- ∀ {α : Type u_1} [_inst_1 : linear_order α] {a b : α}, a ≤ b → min a b = a
#check le_of_not_ge -- ∀ {α : Type u} [inst : LinearOrder α] {a b : α}, ¬a ≥ b → a ≤ b
#check List.ne_nil_of_mem -- ∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ []


/-- 
Smallest member of a non-empty list of elements of a linearly ordered type.
-/
def smallest (l: List α)(h : l ≠ []): α := 
  match l with
  | [] => by contradiction
  | head :: tail => 
    if c:tail = []
    then head
    else 
      min head (smallest tail c)

/--
The result of `smallest` is a member of the list.
-/
theorem smallest_mem (l : List α) (hyp : l ≠ []) : 
  smallest l hyp ∈ l := by
  match l with
  | head :: tail => 
    simp [smallest]
    split 
    · rename_i h
      simp [h]
      intro contra
      contradiction
    · rename_i h
      by_cases h':(head ≤ smallest tail h)      
      · simp [h']
      · simp [h', h]
        have lem : 
          min head (smallest tail h) = smallest tail h :=   by 
            apply min_eq_right
            apply le_of_not_ge
            exact h'
        rw [lem] 
        exact smallest_mem tail h



/--
The result of `smallest` is `≤` every member of the list.
-/
theorem smallest_le (l : List α) (hyp : l ≠ []) : 
  ∀ a : α, a ∈ l → smallest l hyp ≤ a  := 
    match l with
  | head :: tail => by
    simp [smallest, hyp]
    apply And.intro
    · split  <;> simp 
    · intro a hyp'
      have c''  := List.ne_nil_of_mem hyp'
      simp [c'']
      right
      exact smallest_le tail c'' a hyp'

#eval smallest [3, 4, 2] (by simp)

-- #eval smallest [(3, 2), (4, 5), (7, 0)]

#eval decide  <| (2, 3) ≤ (3, 2) -- false
#eval decide  <| (2, 3) ≤ (3, 3) -- true


namespace Lexicographic

variable {α β : Type}[LinearOrder α] [LinearOrder β]

scoped instance lexLE : LE (α × β) where
  le := fun (a₁, b₁) (a₂, b₂) ↦
    a₁ ≤ a₂ ∧ (a₁ < a₂ ∨ b₁ ≤ b₂) 

scoped instance LexLT : LT (α × β) where
  lt x y := (x ≤ y) ∧  (¬ y ≤ x)


scoped instance : LinearOrder (α × β) where
  le := fun (a₁, b₁) (a₂, b₂) ↦
    a₁ ≤ a₂ ∧ (a₁ < a₂ ∨ b₁ ≤ b₂) 
  le_refl := by 
    intro (a, b)
    simp 
  le_trans := by
    intro (a₁, b₁) (a₂, b₂) (a₃, b₃)
    simp 
    intro h₁ h₂ h₃ h₄
    simp [le_trans h₁ h₃]
    cases h₂ with
    | inl h => 
      left
      apply lt_of_lt_of_le h
      assumption      
    | inr h => 
      cases h₄ with
      | inl h' => 
        left
        apply lt_of_le_of_lt h₁ 
        assumption
      | inr h' => 
        right
        trans b₂ <;> assumption
  le_antisymm := by
    intro (a₁, b₁) (a₂, b₂) 
    simp 
    intro h₁ h₂ h₃ h₄
    let h₅ := le_antisymm h₁ h₃
    simp [h₅] at *
    exact le_antisymm h₂ h₄

  le_total := by
    intro (a₁, b₁) (a₂, b₂)
    simp 
    by_cases c:a₁ ≤ a₂
    · simp [c]
      by_cases c':a₁ = a₂
      · simp [c', le_total]
      · left
        left
        apply lt_of_le_of_ne c c'
    · right
      simp [le_of_not_ge c, lt_of_not_ge c]

  decidableLE := by
    intro (a₁, b₁) (a₂, b₂)
    by_cases c:a₁ ≤ a₂
    · simp [c]
      by_cases c':a₁ = a₂
      · simp [c', le_total]
        apply inferInstance
      · apply isTrue
        left
        apply lt_of_le_of_ne c c'
    · apply isFalse
      simp [le_of_not_ge c, lt_of_not_ge c]
      simp [c]

#eval smallest [(3, 2), (4, 5), (7, 0)] (by simp) -- (3, 2)

end Lexicographic

open Lexicographic

#eval smallest [(3, 2, 20), (4, 1, 5), (7, 1, 0), (3, 2, 10)] (by simp) -- (3, 2, 10)

#eval decide  <| (2, 3) ≤ (3, 2) -- true
