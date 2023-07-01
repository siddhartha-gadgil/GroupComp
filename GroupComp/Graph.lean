import Mathlib

variable {V E: Type}

structure Graph (V E : Type) where
  ι : E → V
  bar : E → E
  bar_involution: ∀ e, bar (bar e) = e
  bar_no_fp : ∀ e, e ≠ bar e 


def Graph.τ  (G : Graph V E) (e : E) : V := G.ι (G.bar e)

@[simp]
theorem initial_bar  (G : Graph V E) (e : E) :  G.ι (G.bar e)= G.τ e := by rfl

@[simp]
theorem terminal_bar  (G : Graph V E) (e : E) :  G.τ (G.bar e) = G.ι e := by 
  rw [Graph.τ, G.bar_involution]


structure EdgeBetween {V E: Type} (G: Graph V E) (v w: V) where
  edge : E
  source : G.ι edge = v
  target : G.τ edge = w

def EdgeBetween.bar {V E: Type} {G: Graph V E} {v w: V} (e: EdgeBetween G v w) : EdgeBetween G w v := 
  { edge := G.bar e.edge
  , source := by simp [e.target]
  , target := by simp [e.source]
  }

theorem bar_involution {V E: Type} {G: Graph V E} {v w: V} (e: EdgeBetween G v w) : 
  e.bar.bar = e := by 
    have lm : e.bar.bar.edge = e.edge := by 
          simp [EdgeBetween.bar, G.bar_involution]
    simp [EdgeBetween.bar, G.bar_involution, lm]


inductive EdgePath  (G : Graph V E) : V → V → Type where
  | nil : ∀ v, EdgePath G v v
  | cons {v w u : V} : (e : EdgeBetween G v w) →  
      (EdgePath G w u) →  EdgePath G v u

namespace EdgePath

def length  {G : Graph V E} {v w : V} (p : EdgePath G v w) : Nat :=
  match p with
  | nil _ => 0
  | cons _ p'  => 1 + p'.length

def concat {G : Graph V E} {v w u : V} (p : EdgePath G v w) (e: EdgeBetween G w u) : EdgePath G v u := 
  match p with
  | nil .(v) => cons e (nil u)      
  | cons  e' p'  => cons e' (concat p' e)

theorem concat_cons {G : Graph V E}{v w u u': V} (e: EdgeBetween G v w) (p: EdgePath G w u)(e': EdgeBetween G u u')  : 
    concat (cons e p) e' = cons e (concat p e') := by rfl

def reverse {G : Graph V E} {v w : V} (p : EdgePath G v w) : EdgePath G w v := 
  match p with
  | nil .(v) => 
      nil v
  | cons  e p  => 
      let tail := reverse p
      concat tail e.bar  

theorem reverse_cons {G: Graph V E}{v w u : V} (e: EdgeBetween G v w) (p: EdgePath G w u) : 
    reverse (cons e p) = concat (reverse p) e.bar := by rfl

theorem reverse_concat {G: Graph V E}{v w u : V} (p: EdgePath G v w) (e: EdgeBetween G w u) : 
    reverse (concat p e) = cons e.bar (reverse p) := by 
    induction p with
    | nil  => 
      rfl
    | cons  e' p ih =>
      simp [concat_cons, reverse_cons, ih]

def append {G: Graph V E}{ v w u : V}
    (p: EdgePath G v w)(q: EdgePath G w u) : EdgePath G v u :=
  match p with
  | nil .(v) => q
  | cons  e' p'  => 
      let tail := append p' q
      cons e' tail 

instance  {G : Graph V E} {v w u : V} : 
  HAppend (EdgePath G v w) (EdgePath G w u) (EdgePath G v u) := 
    ⟨append⟩

theorem cons_append {G : Graph V E}{v' v w u : V}
    (e: EdgeBetween G v' v)(p: EdgePath G v w)(q: EdgePath G w u) :
    (cons e p) ++ q = cons e (p ++ q) := by rfl

theorem append_assoc {G: Graph V E}{ v w u u' :  V}
  (p: EdgePath G v w)(q: EdgePath G w u)(r: EdgePath G u u') : 
    (p ++ q) ++ r = p ++ (q ++ r) := by 
    induction p with
    | nil  => 
      rfl
    | cons  e' p' ih =>
      simp [cons_append, ih]


theorem reverse_reverse  {G : Graph V E} {v w : V} (p : EdgePath G v w) : 
  p.reverse.reverse = p := by
  induction p with
  | nil  => 
    rfl
  | cons  e p ih => 
    simp [reverse, reverse_cons, reverse_concat, ih, bar_involution]

inductive Reduction  {G : Graph V E} {v w : V}:
      (EdgePath G v w) →  (EdgePath G v w) →  Prop where
  | step {u u' : V}(e : EdgeBetween G u u') (p₁ : EdgePath G v u) (p₂ : EdgePath G u w) : 
      Reduction (p₁ ++ (cons e (cons e.bar p₂))) (p₁ ++ p₂)

def reduced {G : Graph V E} {v w : V} (p : EdgePath G v w) : Prop := 
  ∀ p', ¬ Reduction p p'

end EdgePath

open EdgePath

abbrev PathClass (G: Graph V E) (v w : V)  := 
    Quot <| @EdgePath.Reduction _ _ G v w

abbrev homotopyClass {G: Graph V E} {v w : V} (p : EdgePath G v w) :
   PathClass G v w  := 
  Quot.mk _ p

notation "[[" p "]]" => homotopyClass p 

theorem left_append_step {G: Graph V E}{v w u : V} (a : EdgePath G v w)  (b₁ b₂ : EdgePath G w u)  (rel : Reduction  b₁ b₂) : 
   [[a ++ b₁]] = [[a ++ b₂]] := by
    induction rel with
    | step e p₁ p₂ => 
      apply Quot.sound
      simp [← EdgePath.append_assoc]
      exact EdgePath.Reduction.step e (a ++ p₁) p₂ 

theorem right_append_step {G: Graph V E}{v w u : V} (a₁ a₂ : EdgePath G v w)  (b : EdgePath G w u) (rel : Reduction  a₁ a₂) : 
    [[a₁ ++ b]] = [[a₂ ++ b]] := by 
    induction rel with
    | step e p₁ p₂ => 
      apply Quot.sound
      simp [EdgePath.append_assoc, EdgePath.cons_append]
      exact EdgePath.Reduction.step e p₁ (p₂ ++ b)


#check Quot.liftOn₂
#check Quot.lift₂

def PathClass.mul {G: Graph V E}{v w u : V} : 
    PathClass G v w → PathClass G w u → PathClass G v u := by
  apply Quot.lift₂ (fun p₁ p₂ ↦ [[ p₁ ++ p₂ ]])
  · intro a b₁ b₂ rel
    apply left_append_step
    assumption
  · intro a b₁ b₂ rel
    apply right_append_step
    assumption


#check Quot.induction_on

instance  {G : Graph V E} {v w u : V} : 
  HMul (PathClass G v w) (PathClass G w u) (PathClass G v u) := 
    ⟨PathClass.mul⟩

namespace PathClass

theorem mul_append {G : Graph V E} {v w u : V} {a: EdgePath G v w} 
  {b  : EdgePath G w u} :
  [[ a ]] * [[ b ]] = [[ a ++ b ]] := by rfl

theorem mul_assoc {G: Graph V E}{ v w u u' :  V}:
  (p: PathClass G v w) → (q: PathClass G w u) → (r: PathClass G u u') →  
    (p * q) * r = p * (q * r) := by 
    apply Quot.ind
    intro a
    apply Quot.ind
    intro b
    apply Quot.ind
    intro c
    simp [mul_append, EdgePath.append_assoc]
end PathClass

def wedgeCircles (S: Type) : Graph Unit (S × Bool) := {
  ι := fun _ => ()
  bar := fun (e, b) ↦ (e, !b)
  bar_involution := fun (e, b) => by intros ; simp
  bar_no_fp := fun (e, b) => by intros ; simp
}

class ConnectedGraph (G: Graph V E) where
  path : (v w: V) → EdgePath G v w

def getPath (G: Graph V E) [ConnectedGraph G] (v w: V) : EdgePath G v w :=
  ConnectedGraph.path v w

/-!
Old stuff
-/

inductive EdgePath'  (G : Graph V E) : V → V → Type where
  | nil : ∀ v, EdgePath' G v v
  | cons {v w u : V} : (e : E) →  
        (EdgePath' G w u) →  G.ι e = v → G.τ e = w  → EdgePath' G v u


namespace EdgePath'

def length  {G : Graph V E} {v w : V} (p : EdgePath' G v w) : Nat :=
  match p with
  | EdgePath'.nil _ => 0
  | EdgePath'.cons _ p' _ _ => 1 + p'.length

def concat {G : Graph V E} {v w u : V} (p : EdgePath' G v w) (e: E)(h₁ : G.ι e = w)(h₂ : G.τ e = u) : EdgePath' G v u := 
  match p with
  | EdgePath'.nil .(v) => 
    EdgePath'.cons e (EdgePath'.nil u) h₁ h₂     
  | EdgePath'.cons  e' p' h₁' h₂' => 
      let tail := EdgePath'.concat p' e h₁ h₂
      EdgePath'.cons e' tail h₁' h₂'

def reverse {G : Graph V E} {v w : V} (p : EdgePath' G v w) : EdgePath' G w v := by
  match p with
  | EdgePath'.nil .(v) => 
    exact EdgePath'.nil v
  | EdgePath'.cons  e p h₁ h₂ => 
      let tail := EdgePath'.reverse p
      apply EdgePath'.concat tail (G.bar e)  
      · simp ; assumption
      · simp ; assumption

def append {G: Graph V E}{ v w e : V}
    (p: EdgePath' G v w)(q: EdgePath' G w e) : EdgePath' G v e :=
  match p with
  | EdgePath'.nil .(v) => q
  | EdgePath'.cons  e' p' h₁ h₂ => 
      let tail := EdgePath'.append p' q
      EdgePath'.cons e' tail h₁ h₂

instance  {G : Graph V E} {v w u : V} : 
  HAppend (EdgePath' G v w) (EdgePath' G w u) (EdgePath' G v u) := 
    ⟨EdgePath'.append⟩

end EdgePath'
