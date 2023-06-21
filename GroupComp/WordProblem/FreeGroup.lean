import Mathlib
/-!
# Word problem in free groups

We translate into Lean the solution to the word problem in free groups based on covering spaces. We use the same definitions and some of the lemmas from the solution in Mathlib4.

The translation is not faithful - we skip definitions of graphs and paths and instead abstract the sequence of vertices along the lift of a path.
-/


variable {α : Type} [DecidableEq α]

#check FreeGroup


namespace FreeGroup
open Red

#check Step -- FreeGroup.Red.Step.{u} {α : Type u} (a✝a✝¹ : List (α × Bool)) : Prop

#check not_step_singleton -- FreeGroup.Red.not_step_singleton.{u} {α : Type u} {L : List (α × Bool)} {p : α × Bool} : ¬Step [p] L

#check not_step_nil -- FreeGroup.Red.not_step_nil.{u} {α : Type u} {L : List (α × Bool)} : ¬Step [] L

abbrev Reduced (L: List (α × Bool)) : Prop := ∀ L' : List (α × Bool), ¬ Step L L' 

theorem reduced_nil : @Reduced α ([]) := by apply not_step_nil

theorem reduced_singleton (p : α × Bool) : @Reduced α ([p]) := by 
  intro L' step
  apply not_step_singleton step  
 
abbrev Letter.inv (p : α × Bool) : α × Bool := (p.1, !p.2)

end FreeGroup

#check List.concat_eq_append -- List.concat_eq_append.{u} {α : Type u} (as : List α) (a : α) : List.concat as a = as ++ [a]

#check List.of_concat_eq_concat -- List.of_concat_eq_concat.{u} {α : Type u} {as bs : List α} {a b : α} (cancP : List.concat as a = List.concat bs b) : as = bs ∧ a = b


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

def nextVertex (start: List (α × Bool))(letter: (α × Bool)) : List (α × Bool) := 
  if nilP:start = [] then [letter]
  else
    let last := start.getLast nilP
    if last = Letter.inv letter then
        start.dropLast
    else
        start.concat (letter)

infixl:65 " :+ " => nextVertex

theorem nil_nextVertex (letter : (α × Bool)) : 
    nextVertex [] letter = [letter] := by rfl

theorem nonnil_nextVertex_extend 
    (start : List (α × Bool)) (nonnil: start ≠ []) (letter : (α × Bool))
    (neq : start.getLast nonnil ≠ Letter.inv letter) : 
    start :+ letter = start.concat letter := by 
  simp [nextVertex,  neq, if_neg, nonnil]

theorem nonnil_nextVertex_cancel (start : List (α × Bool)) 
    (nonnil: start ≠ []) (letter : (α × Bool)) 
    (eql : start.getLast nonnil = Letter.inv letter) : 
    start :+ letter = start.dropLast  := by 
  simp [nextVertex,  eql, if_pos, nonnil]

theorem exists_of_step {L L': List (α × Bool)} :
    Step L L' → ∃ x : α , ∃  b : Bool, ∃ L₁ L₂ : List (α × Bool ),
    L = (L₁ ++ (x, b) :: (x, !b) :: L₂) ∧ L' = L₁ ++ L₂  := by
  intro step
  induction step with
  | @not L₁ L₂ x b =>  use x, b, L₁, L₂; simp

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
    if cancP:start.getLast nilP = Letter.inv letter 
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
      if endP : L₂ = [] then
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
        simp [Letter.inv] at cancP
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

abbrev equiv (a b : List (α × Bool)) := mk a = mk b

infix:50 " ∼ " => equiv

theorem homotopy_lifting_endpoints(start: List (α × Bool))(a : α)(b: Bool):
    Reduced start → start :+ (a, b) :+ (a, !b) = start := by
  intro reduced_start
  if nilP: start = [] then
    simp [nilP, nextVertex, Letter.inv]
  else 
    if cancP:start.getLast nilP = Letter.inv (a, b) 
    then 
      simp [cancP, nonnil_nextVertex_cancel, nilP]
      if nil' : start.dropLast = [] then
        simp [nilP, nil', nil_nextVertex]
        let sp := split_drop start nilP
        rw [←sp, nil']
        simp
        simp [Letter.inv] at cancP
        rw [cancP]
      else
        if cancP':start.dropLast.getLast nil'  = Letter.inv (a, !b) then
          let sp := split_drop start nilP
          let sp' := split_drop start.dropLast nil'
          rw [←sp', cancP', cancP] at sp
          have : Letter.inv (a, b) = (a, !b) := by
            rfl
          rw [this] at sp
          have : Letter.inv (a, !b) = (a, b) := by
            simp [Letter.inv]
          rw [this] at sp
          let L' := start.dropLast.dropLast
          have : 
            List.dropLast (List.dropLast start) ++ [(a, b)] ++ [(a, !b)] = L' ++ (a, b) :: (a, !b) :: [] := by
            simp
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
          have : Letter.inv (a, b) = (a, !b) := by
            rfl
          rw [this] at cancP
          let sp := split_drop start nilP
          rw [cancP] at sp
          simp [Letter.inv] at cancP
          simp [sp]
    else
      simp [cancP, nonnil_nextVertex_extend]
      have eqn : start :+ (a, b) = start.concat (a, b) := by 
        simp [nonnil_nextVertex_extend, cancP, nilP]
      have nn : start :+ (a, b) ≠ [] := by 
        simp [eqn]
      let cnc := 
        nonnil_nextVertex_cancel (start :+ (a, b)) nn (a, !b)
        (by 
          simp [Letter.inv, cancP, eqn]) 
      rw [cnc, eqn]
      simp

theorem nextVertex_equiv_concat
    (start: List (α × Bool))(letter: (α × Bool)):
    start.concat letter ∼  start :+ letter  := by
  if nilP: start = [] then
    simp [nilP, nil_nextVertex]
  else
    if cancP:start.getLast nilP = Letter.inv letter
    then
      simp [cancP, nonnil_nextVertex_cancel, nilP]
      let (a, b) := letter
      apply Quot.sound
      simp [Letter.inv] at cancP
      let sp := split_drop start nilP
      rw [cancP] at sp
      let step' := @Step.not _ start.dropLast ([]) a !b
      have : List.dropLast start ++ [(a, !b), (a, b)] = 
        start.dropLast ++ [(a, !b)] ++ [(a, b)] := by simp
      simp [this, sp] at step'
      exact step'
    else
      simp [cancP, nonnil_nextVertex_extend, nilP]
        
def finalVertex (start word : List (α × Bool)) : List (α × Bool) :=
  List.foldl (nextVertex) start word

theorem finalVertex_reduced (start word : List (α × Bool)) :
    Reduced start → Reduced (finalVertex start word) := 
  fun reduced_start ↦
  match word with
  | [] => reduced_start
  | head  :: tail  =>
    finalVertex_reduced (start :+ head) tail 
      (nextVertex_reduced start head reduced_start)

theorem append_equiv {L₁ L₂ : List (α × Bool)}(L₃ : List (α × Bool)) :
    L₁ ∼ L₂ → L₁ ++ L₃ ∼ L₂ ++ L₃ := by
  intro eqn
  show mk (L₁ ++ L₃) = mk (L₂ ++ L₃)
  rw [← mul_mk, ← mul_mk]
  rw [eqn]
     
theorem finalVertex_equiv_append (start word : List (α × Bool)) :
    start ++ word ∼ finalVertex start word  := by
  match word with
  | [] => simp [finalVertex]
  | head ::tail => 
    simp [finalVertex, List.foldl_cons]
    let ih := finalVertex_equiv_append (start :+ head) tail
    simp [finalVertex, List.foldl_cons] at ih
    let eqn := nextVertex_equiv_concat start head
    show mk (start ++ head :: tail) = mk (List.foldl nextVertex (start :+ head) tail)
    rw [←ih]
    let eqn' := append_equiv tail eqn
    simp [← eqn']
      

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

theorem finalVertexOnFreeGroup_natural (start word : List (α × Bool)) 
    (red : Reduced start) : 
  finalVertex start word = finalVertexOnFreeGroup start red (mk word) := by rfl

abbrev reducedWord (g : FreeGroup α) := finalVertexOnFreeGroup [] reduced_nil g

theorem reducedWord_inverse 
    (g : FreeGroup α) : mk (reducedWord g) = g := by
  apply Quot.ind (β := fun g ↦ mk (reducedWord g) = g )
  intro word
  simp [finalVertex_equiv_append [], ←finalVertexOnFreeGroup_natural]
  simp [←finalVertex_equiv_append]

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
