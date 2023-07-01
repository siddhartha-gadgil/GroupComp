import Mathlib.Data.Bool.Basic
import Mathlib.CategoryTheory.Groupoid

universe u v

structure Graph (V : Type u) (E : Type v) where
  ι : E → V
  bar : E → E
  bar_involution : ∀ e, bar (bar e) = e
  bar_no_fp : ∀ e, e ≠ bar e

namespace Graph

variable {V : Type u} {E : Type v} (G : Graph V E)
variable {u v w : V}

attribute [simp] bar_involution

def τ (e : E) : V := G.ι (G.bar e)

@[simp] theorem ι_bar (e : E) :  G.ι (G.bar e) = G.τ e := rfl

@[simp] theorem τ_bar (e : E) :  G.τ (G.bar e) = G.ι e := by
  aesop (add norm unfold [τ])

@[ext] structure EdgeBetween (v w : V) where
  edge : E
  source : G.ι edge = v
  target : G.τ edge = w

attribute [aesop safe forward] EdgeBetween.source EdgeBetween.target

variable {G} (e : G.EdgeBetween v w)

def EdgeBetween.bar (e : G.EdgeBetween v w) : G.EdgeBetween w v := 
  { edge := G.bar e.edge
  , source := by aesop
  , target := by aesop
  }

@[simp] theorem EdgeBetween.bar_involution : e.bar.bar = e := by 
    ext; aesop (add norm simp [EdgeBetween.bar])

-- @[aesop unsafe [cases, constructors]]
inductive EdgePath (G : Graph V E) : V → V → Type _ where
  | nil (v) : G.EdgePath v v
  | cons {v w u} : G.EdgeBetween v w → G.EdgePath w u → G.EdgePath v u

namespace EdgePath

def length {v w : V} : G.EdgePath v w → ℕ
  | nil _ => 0
  | cons _ p'  => p'.length.succ

def concat {v w u : V} (p : G.EdgePath v w) (e : G.EdgeBetween w u) : G.EdgePath v u := 
  match p with
  | nil .(v) => cons e (nil u)      
  | cons  e' p'  => cons e' (concat p' e)

@[simp] theorem concat_cons {v w u u': V} (e: G.EdgeBetween v w) (p: G.EdgePath w u) (e': G.EdgeBetween u u')  : 
    concat (cons e p) e' = cons e (concat p e') := by rfl

def reverse {v w : V} (p : G.EdgePath v w) : G.EdgePath w v := 
  match p with
  | nil .(v) => 
      nil v
  | cons  e p  => 
      let tail := reverse p
      concat tail e.bar  

@[simp] theorem reverse_nil {v : V} : 
  reverse (.nil (G := G) v) = .nil (G := G) v := by rfl

theorem reverse_cons {v w u : V} (e : G.EdgeBetween v w) (p : G.EdgePath w u) : 
    reverse (cons e p) = concat (reverse p) e.bar := by rfl

theorem reverse_concat {v w u : V} (p: G.EdgePath v w) (e: G.EdgeBetween w u) : 
    reverse (concat p e) = cons e.bar (reverse p) := by 
    induction p <;> aesop (add norm simp [concat_cons, reverse_cons])

def append { v w u : V}
    (p : G.EdgePath v w) (q : G.EdgePath w u) : G.EdgePath v u :=
  match p with
  | nil .(v) => q
  | cons  e' p'  => 
      let tail := append p' q
      cons e' tail 

instance  G.EdgePath {v w u : V} {G : Graph V E} : 
  HAppend (G.EdgePath v w) (G.EdgePath w u) (G.EdgePath v u) := 
    ⟨append⟩

@[simp] theorem nil_append  {u v : V} (p: G.EdgePath u v) :
  EdgePath.nil (G := G) u ++ p = p := rfl

@[simp] theorem append_nil  {u v : V} (p: G.EdgePath u v) :
  p ++ EdgePath.nil (G := G) v = p := by
    show append _ _ = _
    induction p <;> aesop (add norm simp [append])

@[simp] theorem cons_append {v' v w u : V}
    (e: G.EdgeBetween v' v)(p: G.EdgePath v w)(q: G.EdgePath w u) :
    (cons e p) ++ q = cons e (p ++ q) := by rfl

@[simp] theorem concat_append { v w w' u : V}
    (e : G.EdgeBetween w w')(p: G.EdgePath v w)(q: G.EdgePath w' u) :
    (concat p e) ++ q = p ++ (cons e q) := by
    induction p <;> aesop

-- theorem append_cons {v w u u' : V}
--     (p: G.EdgePath v w)(e: G.EdgeBetween w u)(q: G.EdgePath u u') :
--     p ++ (cons e q) = cons e (p ++ q) := by 
--     induction p with
--     | nil  => 
--       rfl
--     | cons  e' p ih =>
--       simp [cons_append, ih]

theorem append_assoc { v w u u' :  V}
  (p: G.EdgePath v w)(q: G.EdgePath w u)(r: G.EdgePath u u') : 
    (p ++ q) ++ r = p ++ (q ++ r) := by 
    induction p <;> aesop

@[simp] theorem reverse_reverse {v w : V} (p : G.EdgePath v w) : 
  p.reverse.reverse = p := by
  induction p <;> aesop (add norm simp [reverse_cons, reverse_concat])

@[aesop safe [constructors, cases]]
inductive Reduction {v w : V}:
      G.EdgePath v w →  G.EdgePath v w →  Prop where
  | step {u u' : V}(e : G.EdgeBetween u u') (p₁ : G.EdgePath v u) (p₂ : G.EdgePath u w) : 
      Reduction (p₁ ++ (cons e (cons e.bar p₂))) (p₁ ++ p₂)

def reduced  {v w : V} (p : G.EdgePath v w) : Prop := 
  ∀ p', ¬ Reduction p p'

end EdgePath

open EdgePath

abbrev PathClass (G: Graph V E) (v w : V)  := 
    Quot <| @EdgePath.Reduction _ _ G v w

abbrev homotopyClass  {v w : V} (p : G.EdgePath v w) :
   PathClass G v w  := 
  Quot.mk _ p

notation "[[" p "]]" => homotopyClass p

attribute [aesop safe apply] Quot.sound

@[simp] theorem cons_bar_cons (e : G.EdgeBetween w v) (p: G.EdgePath w u) :
    [[p |>.cons e.bar |>.cons e]] = [[p]] := by
  have := Reduction.step e (.nil w) p
  aesop

@[simp] theorem cons_cons_bar (e : G.EdgeBetween v w) (p: G.EdgePath w u) : 
  [[p |>.cons e |>.cons e.bar]] = [[p]] := by
  have := cons_bar_cons e.bar p
  aesop

theorem left_append_step {v w u : V} (a : G.EdgePath v w)  (b₁ b₂ : G.EdgePath w u)  (rel : Reduction  b₁ b₂) : 
   [[a ++ b₁]] = [[a ++ b₂]] := by
    induction rel with
    | step e p₁ p₂ => 
      apply Quot.sound
      simp [← EdgePath.append_assoc]
      exact .step e (a ++ p₁) p₂ 

theorem right_append_step {v w u : V} (a₁ a₂ : G.EdgePath v w)  (b : G.EdgePath w u) (rel : Reduction  a₁ a₂) : 
    [[a₁ ++ b]] = [[a₂ ++ b]] := by
  aesop (add norm simp [append_assoc])

@[simp] theorem reverse_left_inverse {v w : V} 
(p : G.EdgePath v w) : 
    [[p.reverse ++ p]] = [[.nil w]] := by
    induction p with
    | nil v  => simp
    | cons e p ih => 
      simp [EdgePath.reverse_cons, EdgePath.reverse_concat, EdgePath.cons_append, ih]
      trans [[reverse p ++ p]]
      · apply Quot.sound
        let step := Reduction.step e.bar (reverse p) p
        simp at step
        assumption
      · assumption

@[simp] theorem reverse_right_inverse {v w : V} (p : G.EdgePath w v) :
    [[p ++ p.reverse]] = [[.nil w]] := by
  have := reverse_left_inverse p.reverse
  aesop

def PathClass.id (G : Graph V E) (v : V) : PathClass G v v :=
  [[.nil v]]

def PathClass.mul {v w u : V} : 
    PathClass G v w → PathClass G w u → PathClass G v u := by
  apply Quot.lift₂ (fun p₁ p₂ ↦ [[ p₁ ++ p₂ ]]) <;>
    aesop (add safe apply [left_append_step, right_append_step])

instance {v w u : V} : 
  HMul (PathClass G v w) (PathClass G w u) (PathClass G v u) := 
    ⟨PathClass.mul⟩

namespace PathClass

@[simp] theorem id_mul  {u v : V} {a : G.EdgePath u v} : 
  (PathClass.id G u) * [[a]] = [[a]] := by rfl

@[simp] theorem mul_id  {u v : V} {a : G.EdgePath u v} : 
  [[a]] * (PathClass.id G v) = [[a]] := by 
  show [[_]] = _
  rw [EdgePath.append_nil]

theorem mul_append  {v w u : V} {a: G.EdgePath v w} 
  {b  : G.EdgePath w u} :
  [[ a ]] * [[ b ]] = [[ a ++ b ]] := by rfl

theorem mul_assoc { v w u u' :  V}:
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
  bar_no_fp := fun (e, b) => by intros ; simp only [ne_eq, Prod.mk.injEq, true_and, Bool.not_eq_not]
}

class ConnectedGraph (G: Graph V E) where
  path : (v w: V) → G.EdgePath v w

def getPath (G: Graph V E) [ConnectedGraph G] (v w: V) : G.EdgePath v w :=
  ConnectedGraph.path v w

instance  : CategoryTheory.Groupoid V where
  Hom := PathClass G
  id := PathClass.id G
  comp := PathClass.mul (G := G)
  id_comp := sorry
  comp_id := sorry
  assoc := sorry
  inv := sorry
  inv_comp := sorry
  comp_inv := sorry

#exit

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

def append { v w e : V}
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
