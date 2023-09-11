import Mathlib
/-!
# Word problem in free groups

We translate into Lean the solution to the word problem in free groups based on covering spaces. We use the same definitions and some of the lemmas from the solution in Mathlib4.

The translation is not faithful - we skip definitions of graphs and paths and instead identify lifts of paths with sequences of vertices. 

The vertices in the universal cover are reduced words in the generators of the free group. A path in wedge of circles is a word in the generators and their inverses. 

* We define the lift of a path as a sequence of vertices.
* We show that the vertices along the path are reduced.
* We show that a reduced word is lifted to itself.
* We show that the lift of a word is equal in the free group to the terminal vertex of its lift.

All this is done by defining and proving properties of the lift on an edge starting at a (reduced) word. The lift of a path is then defined as the concatenation of the lifts of its edges.
-/


variable {α : Type} [DecidableEq α]

#check FreeGroup


namespace FreeGroup
open Red

#check Step -- FreeGroup.Red.Step.{u} {α : Type u} (a✝a✝¹ : List (α × Bool)) : Prop

#check not_step_singleton -- FreeGroup.Red.not_step_singleton.{u} {α : Type u} {L : List (α × Bool)} {p : α × Bool} : ¬Step [p] L

#check not_step_nil -- FreeGroup.Red.not_step_nil.{u} {α : Type u} {L : List (α × Bool)} : ¬Step [] L

/--
Proposition that a word is reduced.
-/
abbrev Reduced (L: List (α × Bool)) : Prop := ∀ L' : List (α × Bool), ¬ Step L L' 

/--
The empty word is reduced.
-/
theorem reduced_nil : @Reduced α ([]) := by apply not_step_nil

/--
A word with a single letter is reduced.
-/
theorem reduced_singleton (p : α × Bool) : @Reduced α ([p]) := by 
  intro L' step
  apply not_step_singleton step  
 
/--
The inverse of a letter.
-/
abbrev Letter.inv (p : α × Bool) : α × Bool := (p.1, !p.2)

instance : Inv (α × Bool) := ⟨Letter.inv⟩

theorem inv_def (p : α × Bool) : p⁻¹ = (p.1, !p.2) := rfl

theorem inv_def' (l : α)(b : Bool) : (l, b)⁻¹ = (l, !b) := rfl

end FreeGroup

#check List.concat_eq_append -- List.concat_eq_append.{u} {α : Type u} (as : List α) (a : α) : List.concat as a = as ++ [a]

#check List.of_concat_eq_concat -- List.of_concat_eq_concat.{u} {α : Type u} {as bs : List α} {a b : α} (cancP : List.concat as a = List.concat bs b) : as = bs ∧ a = b

/--
For a non-empty list, appending the last element to the list obtained by `dropLast` is the same as the original list.
-/
theorem split_drop (l: List β)(p : l ≠ []) :
    l.dropLast ++ [l.getLast p] = l := by
    match l with
    | cancP :: t =>
    match t with 
    | [] =>  simp [p] at *
    | h' :: t' =>
      simp [List.dropLast, List.getLast, split_drop]

namespace FreeGroup
open Red

/--
The next vertex in the lift of a path with given initial word and edge to lift. The definition does not require the initial word to be reduced, but the properties do.
-/
def nextVertex (start: List (α × Bool))(letter: (α × Bool)) : List (α × Bool) := 
  if nilP:start = [] then [letter]
  else
    let last := start.getLast nilP
    if last = letter⁻¹ then
        start.dropLast
    else
        start.concat (letter)

infixl:65 " :+ " => nextVertex

/--
Lift of an edge at the empty word.
-/
theorem nil_nextVertex (letter : (α × Bool)) : 
    nextVertex [] letter = [letter] := by rfl

/--
Lift of an edge where we do not cancel the last letter.
-/
theorem nonnil_nextVertex_extend 
    (start : List (α × Bool)) (nonnil: start ≠ []) (letter : (α × Bool))
    (neq : start.getLast nonnil ≠ letter⁻¹) : 
    start :+ letter = start.concat letter := by 
  simp [nextVertex,  neq, if_neg, nonnil]

/--
Lift of an edge where we cancel the last letter.
-/
theorem nonnil_nextVertex_cancel (start : List (α × Bool)) 
    (nonnil: start ≠ []) (letter : (α × Bool)) 
    (eql : start.getLast nonnil = letter⁻¹) : 
    start :+ letter = start.dropLast  := by 
  simp [nextVertex,  eql, if_pos, nonnil]

/--
To avoid subtleties with indices, we extract from a step the letter and the two parts of the list around it as well as the relation.
-/
theorem exists_of_step {L L': List (α × Bool)} :
    Step L L' → ∃ x : α , ∃  b : Bool, ∃ L₁ L₂ : List (α × Bool ),
    L = (L₁ ++ (x, b) :: (x, !b) :: L₂) ∧ L' = L₁ ++ L₂  := by
  intro step
  induction step with
  | @not L₁ L₂ x b =>  use x, b, L₁, L₂

/--
If we lift an edge starting at a reduced word, the result is reduced.
-/
theorem nextVertex_reduced (start: List (α × Bool))(letter: (α × Bool)):
    Reduced start → Reduced (start :+ letter) := by
  intro reduced_start
  if nilP: start = [] 
  then 
    simp [nil_nextVertex, nilP]
    apply reduced_singleton
  else
    intro L' step
    let ⟨x, b, L₁, L₂, eqs⟩ := exists_of_step step
    let eq1 := eqs.1
    if cancP:start.getLast nilP = letter⁻¹ 
    then 
      simp [cancP, nilP, nonnil_nextVertex_cancel] at eq1
      have eq1' : start.dropLast.concat (start.getLast nilP) = 
          (L₁ ++ (x, b) :: (x, !b) :: L₂).concat (start.getLast nilP) :=
        by rw [eq1]
      simp [split_drop, nilP] at eq1'
      let L₂' := L₂ ++ [start.getLast nilP]
      apply reduced_start (L₁ ++ L₂')
      rw [eq1']
      apply Step.not
    else 
      simp [cancP, nilP, nonnil_nextVertex_extend] at eq1
      if endP : L₂ = [] 
      then
        simp [endP] at eq1
        rw [←List.concat_eq_append] at eq1
        have : L₁ ++ [(x, b), (x, !b)] = 
          (L₁ ++ [(x, b)]).concat (x, !b) := by simp
        rw [this] at eq1
        let eq1' := List.of_concat_eq_concat eq1
        let eq1'' := eq1'.1
        let sp := split_drop start nilP
        rw [← sp, ←List.concat_eq_append, ←List.concat_eq_append] at eq1''
        let eq1''' := eq1'.2
        let eq2' := List.of_concat_eq_concat eq1''
        let _eq2'' := eq2'.2
        rw [eq1''', _eq2''] at cancP
        simp [inv_def] at cancP
      else
        rw [← split_drop L₂ endP] at eq1
        rw [← List.cons_append, ← List.cons_append, 
          ← List.append_assoc, ← List.concat_eq_append,
          ← List.concat_eq_append] at eq1
        let eq1' := List.of_concat_eq_concat eq1
        let eq1'' := eq1'.1
        apply reduced_start (L₁ ++ L₂.dropLast)
        rw [eq1'']
        apply Step.not

/--
Words are equivalent if they represent the same element of the free group.
-/
abbrev equiv (a b : List (α × Bool)) := mk a = mk b

infix:50 " ∼ " => equiv

#check Bool.not_not
/--
Lifting by two edges that are inverses of each other does not change the word if the initial word is reduced. This is the part of homotopy lifting we need.
-/
theorem homotopy_lifting_endpoints(start: List (α × Bool))(a : α)(b: Bool):
    Reduced start → start :+ (a, b) :+ (a, !b) = start := by
  intro reduced_start
  if nilP: start = [] then
    simp [nilP, nextVertex, inv_def]
  else 
    if cancP:start.getLast nilP = (a, b)⁻¹ 
    then 
      simp [cancP, nonnil_nextVertex_cancel, nilP]
      if nil' : start.dropLast = [] 
      then
        simp [nilP, nil', nil_nextVertex]
        let sp := split_drop start nilP
        rw [←sp, nil']
        simp
        simp [inv_def] at cancP
        rw [cancP]
      else
        if cancP':start.dropLast.getLast nil'  = (a, !b)⁻¹ 
        then
          let sp := split_drop start nilP
          let sp' := split_drop start.dropLast nil'
          rw [←sp', cancP', cancP] at sp
          simp [inv_def' a !b] at sp
          let L' := start.dropLast.dropLast
          have : 
            List.dropLast (List.dropLast start) ++ [(a, b), (a, b)⁻¹] = L' ++ (a, b) :: (a, !b) :: [] := by simp [inv_def]
          rw [this] at sp
          have step : Step start (L' ++ []) := by
            rw [← sp]
            show Step (L' ++ (a, b) :: (a, !b) :: []) (L' ++ [])
            apply Step.not
          apply False.elim
          apply reduced_start
          exact step
        else
          let res := 
            nonnil_nextVertex_extend start.dropLast nil' (a, !b) cancP'    
          rw [res]
          let sp := split_drop start nilP
          rw [cancP] at sp
          simp [inv_def] at cancP
          simp [inv_def] at sp 
          simp [sp]
    else
      have eqn : start :+ (a, b) = start.concat (a, b) := by 
        simp [nonnil_nextVertex_extend, cancP, nilP]
      have nn : start :+ (a, b) ≠ [] := by 
        simp [eqn]
      let cnc := 
        nonnil_nextVertex_cancel (start :+ (a, b)) nn (a, !b)
        (by 
          simp [inv_def, cancP, eqn]) 
      rw [cnc, eqn]
      simp

/--
The next vertex of the lift starting at a reduced word is equivalent to the word with the next vertex added.
-/
theorem nextVertex_homotopic_concat
    (start: List (α × Bool))(letter: (α × Bool)):
    start.concat letter ∼  start :+ letter  := by
  if nilP: start = [] then
    simp [nilP, nil_nextVertex]
  else
    if cancP:start.getLast nilP = letter⁻¹
    then
      simp [cancP, nonnil_nextVertex_cancel, nilP]
      let (a, b) := letter
      apply Quot.sound
      let sp := split_drop start nilP
      rw [cancP] at sp
      let step' := @Step.not _ start.dropLast ([]) a !b
      simp [Bool.not_not] at step'
      have : List.dropLast start ++ [(a, !b), (a, b)] = 
        start.dropLast ++ [(a, !b)] ++ [(a, b)] := by simp
      rw [inv_def] at sp
      rw [this, sp] at step'
      exact step'
    else
      simp [cancP, nonnil_nextVertex_extend, nilP]

/--
The final vertex on lifting a word starting at an initial (reduced) word.
-/        
def finalVertex (start word : List (α × Bool)) : List (α × Bool) :=
  List.foldl (nextVertex) start word

/--
The final vertex of a lift starting at a reduced word is reduced.
-/
theorem finalVertex_reduced (start word : List (α × Bool)) :
    Reduced start → Reduced (finalVertex start word) := 
  fun reduced_start ↦
  match word with
  | [] => reduced_start
  | head  :: tail  =>
    finalVertex_reduced (start :+ head) tail 
      (nextVertex_reduced start head reduced_start)

/--
If words are equivalent then the results of appending a word to them are equivalent.
-/
theorem append_homotopic {L₁ L₂ : List (α × Bool)}(L₃ : List (α × Bool)) :
    L₁ ∼ L₂ → L₁ ++ L₃ ∼ L₂ ++ L₃ := by
  intro eqn
  show mk (L₁ ++ L₃) = mk (L₂ ++ L₃)
  rw [← mul_mk, ← mul_mk]
  rw [eqn]
     
/--
The final vertex of a lift starting at a reduced word is equivalent to the result of appending the word to the initial word.
-/
theorem finalVertex_homotopic_append (start word : List (α × Bool)) :
    start ++ word ∼ finalVertex start word  := by
  match word with
  | [] => simp [finalVertex]
  | head ::tail => 
    simp [finalVertex, List.foldl_cons]
    let ih := finalVertex_homotopic_append (start :+ head) tail
    simp [finalVertex, List.foldl_cons] at ih
    let eqn := nextVertex_homotopic_concat start head
    show mk (start ++ head :: tail) = mk (List.foldl nextVertex (start :+ head) tail)
    rw [←ih]
    let eqn' := append_homotopic tail eqn
    simp [← eqn']
      
/--
Induced map on the free group corresponding to lifting. The existence and naturality show that equivalent words lift to paths with the same endpoint.
-/
def finalVertexOnFreeGroup (start : List (α × Bool)) (red : Reduced start) 
    (g: FreeGroup α) : List (α × Bool) := by
  apply Quot.liftOn g (finalVertex start)
  intro w₁ w₂ step
  simp [finalVertex]
  let ⟨x, b, L₁, L₂, eqs⟩ := exists_of_step step
  let eq1 := eqs.1
  let eq2 := eqs.2
  rw [eq1, eq2]
  simp [List.foldl_cons, List.foldl_append]
  congr
  apply homotopy_lifting_endpoints
  apply finalVertex_reduced
  assumption

/--
Naturality of the induced map on the free group corresponding to lifting.
-/
theorem finalVertexOnFreeGroup_natural (start word : List (α × Bool)) 
    (red : Reduced start) : 
  finalVertex start word = finalVertexOnFreeGroup start red (mk word) := by rfl

/--
We map an element of the free group to a reduced word.
-/
abbrev reducedWord (g : FreeGroup α) := 
  finalVertexOnFreeGroup [] reduced_nil g

/--
The reduced word to which an element in the free group maps represents the element.
-/
theorem reducedWord_inverse 
    (g : FreeGroup α) : mk (reducedWord g) = g := by
  apply Quot.ind (β := fun g ↦ mk (reducedWord g) = g )
  intro word
  simp [finalVertex_homotopic_append [], ←finalVertexOnFreeGroup_natural]
  simp [←finalVertex_homotopic_append]

/--
Decidability of the word problem for free groups.
-/
instance wordProblem : DecidableEq (FreeGroup α) := by
  intro a b
  if c:reducedWord a = reducedWord b
  then
    apply isTrue
    let lm := congrArg mk c
    simp [reducedWord_inverse] at lm
    exact lm
  else
    apply isFalse
    intro contra
    simp [contra] at c


/- Examples -/
def a : FreeGroup (Fin 2) := mk [(0, false)]
def b : FreeGroup (Fin 2) := mk [(1, false)]

#eval decide (a = b⁻¹)
#eval decide (a * b * b⁻¹ = a) -- true
#eval decide (a * b * b⁻¹ * a⁻¹ = 1) -- true

example : a * b * b⁻¹ * a⁻¹ = 1 := by decide
example : a * b * a⁻¹ * b⁻¹ ≠ 1 := by decide 
