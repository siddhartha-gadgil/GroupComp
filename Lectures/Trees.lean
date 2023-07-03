import Mathlib

inductive TypeTree (α : Type u) : Type u
  | leaf : α → TypeTree α 
  | node : β → (β → TypeTree α)  → TypeTree α 

