import Mathlib

structure Graph (V E : Type) where
  ι : E → V
  bar : E → E
  bar_involution: ∀ e, bar (bar e) = e
  bar_no_fp : ∀ e, e ≠ bar e 


def Graph.τ {V E : Type} (G : Graph V E) (e : E) : V := G.ι (G.bar e)

@[simp]
theorem initial_bar {V E : Type} (G : Graph V E) (e : E) :  G.ι (G.bar e)= G.τ e := by rfl

@[simp]
theorem terminal_bar {V E : Type} (G : Graph V E) (e : E) :  G.τ (G.bar e) = G.ι e := by 
  rw [Graph.τ, G.bar_involution]

inductive EdgePath {V E : Type} (G : Graph V E) : V → V → Type where
  | nil : ∀ v, EdgePath G v v
  | cons {v w u : V} : (e : E) →  
        (EdgePath G w u) →  G.ι e = v → G.τ e = w  → EdgePath G v u


namespace EdgePath

def length {V E : Type} {G : Graph V E} {v w : V} (p : EdgePath G v w) : Nat :=
  match p with
  | EdgePath.nil _ => 0
  | EdgePath.cons _ p' _ _ => 1 + p'.length

def concat {V E : Type}{G : Graph V E} {v w u : V} (p : EdgePath G v w) (e: E)(h₁ : G.ι e = w)(h₂ : G.τ e = u) : EdgePath G v u := 
  match p with
  | EdgePath.nil .(v) => 
    EdgePath.cons e (EdgePath.nil u) h₁ h₂     
  | EdgePath.cons  e' p' h₁' h₂' => 
      let tail := EdgePath.concat p' e h₁ h₂
      EdgePath.cons e' tail h₁' h₂'

def reverse {V E : Type}{G : Graph V E} {v w : V} (p : EdgePath G v w) : EdgePath G w v := by
  match p with
  | EdgePath.nil .(v) => 
    exact EdgePath.nil v
  | EdgePath.cons  e p h₁ h₂ => 
      let tail := EdgePath.reverse p
      apply EdgePath.concat tail (G.bar e)  
      · simp ; assumption
      · simp ; assumption

def append {V E : Type}{G: Graph V E}{ v w e : V}
    (p: EdgePath G v w)(q: EdgePath G w e) : EdgePath G v e :=
  match p with
  | EdgePath.nil .(v) => q
  | EdgePath.cons  e' p' h₁ h₂ => 
      let tail := EdgePath.append p' q
      EdgePath.cons e' tail h₁ h₂

instance {V E : Type} {G : Graph V E} {v w u : V} : 
  HAppend (EdgePath G v w) (EdgePath G w u) (EdgePath G v u) := 
    ⟨EdgePath.append⟩

end EdgePath

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


inductive EdgePath' {V E : Type} (G : Graph V E) : V → V → Type where
  | nil : ∀ v, EdgePath' G v v
  | cons {v w u : V} : (e : EdgeBetween G v w) →  
      (EdgePath' G w u) →  EdgePath' G v u

namespace EdgePath'

def length {V E : Type} {G : Graph V E} {v w : V} (p : EdgePath' G v w) : Nat :=
  match p with
  | nil _ => 0
  | cons _ p'  => 1 + p'.length

def concat {V E : Type}{G : Graph V E} {v w u : V} (p : EdgePath' G v w) (e: EdgeBetween G w u) : EdgePath' G v u := 
  match p with
  | nil .(v) => cons e (nil u)      
  | cons  e' p'  => cons e' (concat p' e)

theorem concat_cons {V E : Type}{G : Graph V E}{v w u u': V} (e: EdgeBetween G v w) (p: EdgePath' G w u)(e': EdgeBetween G u u')  : 
    concat (cons e p) e' = cons e (concat p e') := by rfl

def reverse {V E : Type}{G : Graph V E} {v w : V} (p : EdgePath' G v w) : EdgePath' G w v := 
  match p with
  | nil .(v) => 
      nil v
  | cons  e p  => 
      let tail := reverse p
      concat tail e.bar  

theorem reverse_cons {V E : Type}{G: Graph V E}{v w u : V} (e: EdgeBetween G v w) (p: EdgePath' G w u) : 
    reverse (cons e p) = concat (reverse p) e.bar := by rfl

theorem reverse_concat {V E : Type}{G: Graph V E}{v w u : V} (p: EdgePath' G v w) (e: EdgeBetween G w u) : 
    reverse (concat p e) = cons e.bar (reverse p) := by 
    induction p with
    | nil  => 
      rfl
    | cons  e' p ih =>
      simp [concat_cons, reverse_cons, ih]

def append {V E : Type}{G: Graph V E}{ v w e : V}
    (p: EdgePath' G v w)(q: EdgePath' G w e) : EdgePath' G v e :=
  match p with
  | nil .(v) => q
  | cons  e' p'  => 
      let tail := append p' q
      cons e' tail 

instance {V E : Type} {G : Graph V E} {v w u : V} : 
  HAppend (EdgePath' G v w) (EdgePath' G w u) (EdgePath' G v u) := 
    ⟨append⟩

theorem reverse_reverse {V E : Type} {G : Graph V E} {v w : V} (p : EdgePath' G v w) : 
  p.reverse.reverse = p := by
  induction p with
  | nil  => 
    rfl
  | cons  e p ih => 
    simp [reverse, reverse_cons, reverse_concat, ih, bar_involution]

inductive Reduction {V E : Type} {G : Graph V E} {v w : V}:
      (EdgePath' G v w) →  (EdgePath' G v w) →  Prop where
  | step {u u' : V}(e : EdgeBetween G u u') (p₁ : EdgePath' G v u) (p₂ : EdgePath' G u w) : 
      Reduction (p₁ ++ (cons e (cons e.bar p₂))) (p₁ ++ p₂)


end EdgePath'