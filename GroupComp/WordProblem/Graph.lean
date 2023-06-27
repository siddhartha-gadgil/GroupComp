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