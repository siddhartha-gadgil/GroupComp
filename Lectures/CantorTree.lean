import Mathlib

/-!
# Non-positive Inductive Types

We see in more detail how inductive types with a non-positive occurence give a contradiction. Lean will not allow us to define such a type `CantorTree`, so we will bypass it by introducing with sorries.

* Another type `CantorTree'` which we pretend is the same as `CantorTree`.
* *coercions* between `CantorTree` and `CantorTree'` which we pretend are the identity.
* theorems that the coercions are inverses of each other.

We then prove (modulo unfixable sorries) absurd theorems about `CantorTree'`.
-/

def CantorTree' : Type := sorry

inductive CantorTree : Type
  | leaf : CantorTree
  | node : (CantorTree' → Bool)  → CantorTree


/-!
We coerce elements between the types `CantorTree` and `CantorTree'` to pretend they are the same.
-/
instance : Coe CantorTree CantorTree' := sorry
instance : Coe CantorTree' CantorTree := sorry

def evilFn : CantorTree' → Bool := fun t ↦ 
match (t : CantorTree) with
| CantorTree.leaf => false
| CantorTree.node f => !(f t)

#check evilFn (CantorTree.node evilFn) -- Bool

/-!
We "prove" with sorries that the coercions are inverses of each other.
-/
theorem coe_eq (t : CantorTree) : 
    ((t : CantorTree') : CantorTree) = t := by sorry

theorem coe_eq' (t : CantorTree') : 
    ((t : CantorTree) : CantorTree') = t := by sorry


/--
We conclude: `evilFn (CantorTree.node evilFn) = !evilFn (CantorTree.node evilFn)`
which is absurd.
-/
theorem evilFn_is_evil:
  evilFn (CantorTree.node evilFn) = !evilFn (CantorTree.node evilFn) := by
  conv => 
    lhs
    rw [evilFn, coe_eq]
  

/-!
The above is based on Cantor's diagonal argument.
-/

theorem cantor_diagonal {α : Type} (f : α → (α → Bool)) : 
  ∃ t : α → Bool, ∀ a : α, t  ≠ f a := by
  use (fun a ↦ !(f a a) )
  intro a h
  let h' := congrFun h a
  by_cases c:f a a <;> simp [c] at h'
  
  
/--
A surjection from `CantorTree` to `CantorTree' → Bool`.
-/
def cantorSurjection : CantorTree → (CantorTree' → Bool)
| CantorTree.leaf => fun _ => false
| CantorTree.node f => f

/--
Proof of surjectivity of function from `CantorTree'` to `CantorTree`.
-/
theorem cantorSurjection_surjective : 
  ∀ f : CantorTree' → Bool, ∃ t : CantorTree, cantorSurjection t = f := by
  intro f
  use CantorTree.node f
  rfl