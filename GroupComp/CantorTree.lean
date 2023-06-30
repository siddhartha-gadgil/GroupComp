import Mathlib

def CantorTree' : Type := sorry

inductive CantorTree : Type
  | leaf : CantorTree
  | node : (CantorTree' → Bool)  → CantorTree

instance : Coe CantorTree CantorTree' := sorry
instance : Coe CantorTree' CantorTree := sorry

def evil : CantorTree' → Bool := fun t ↦ 
match (t : CantorTree) with
| CantorTree.leaf => false
| CantorTree.node f => !(f t)

#check evil (CantorTree.node evil)

theorem coe_eq (t : CantorTree) : 
    ((t : CantorTree') : CantorTree) = t := by sorry

theorem coe_eq' (t : CantorTree') : 
    ((t : CantorTree) : CantorTree') = t := by sorry


/--
We conclude: `evil (CantorTree.node evil) = !evil (CantorTree.node evil)`
which is absurd.
-/
theorem evil_is_evil:
  evil (CantorTree.node evil) = !evil (CantorTree.node evil) := by
  conv => 
    lhs
    rw [evil, coe_eq]
  

/-!
We conclude: `evil (CantorTree.node evil) = !evil (CantorTree.node evil)`
which is absurd.

This is based on Cantor's diagonal argument.
-/

theorem cantor_diagonal {α : Type} (f : α → (α → Bool)) : 
  ∃ t : α → Bool, ∀ a : α, t  ≠ f a := by
  use (fun a ↦ !(f a a) )
  intro a h
  let h' := congrFun h a
  by_cases c:f a a <;> simp [c] at h'
  
  
#check Function.bijective_iff_existsUnique

def cantorSurjection : CantorTree → (CantorTree' → Bool)
| CantorTree.leaf => fun _ => false
| CantorTree.node f => f

theorem cantorSurjection_surjective : 
  ∀ f : CantorTree' → Bool, ∃ t : CantorTree, cantorSurjection t = f := by
  intro f
  use CantorTree.node f
  rfl