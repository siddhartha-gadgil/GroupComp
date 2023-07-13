import Mathlib.Data.Bool.Basic
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Algebra.Group.Basic
import Mathlib.CategoryTheory.Endomorphism
import Mathlib

universe u v

@[class] structure Graph (V : Type u) (E : Type v) where
  ι : E → V
  bar : E → E
  bar_involution : ∀ e, bar (bar e) = e
  bar_no_fp : ∀ e, e ≠ bar e

namespace Graph

variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
(G : Graph V E)
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
deriving DecidableEq

attribute [aesop safe forward] EdgeBetween.source EdgeBetween.target

variable {G} (e : G.EdgeBetween v w)

def EdgeBetween.bar (e : G.EdgeBetween v w) : G.EdgeBetween w v := 
  { edge := G.bar e.edge
  , source := by aesop
  , target := by aesop
  }

def EdgeBetween.ofEdge (e : E) : G.EdgeBetween (G.ι e) (G.τ e) where
  edge := e
  source := rfl
  target := rfl

@[simp] lemma EdgeBetween.ofEdge_edge (e : E) : 
  (EdgeBetween.ofEdge (G := G) e).edge = e := rfl

@[simp] theorem EdgeBetween.bar_def : e.bar.edge = G.bar e.edge := rfl

@[simp] theorem EdgeBetween.bar_involution : e.bar.bar = e := by 
    ext; aesop (add norm simp [EdgeBetween.bar])

-- @[aesop unsafe [cases, constructors]]
inductive EdgePath (G : Graph V E) : V → V → Type _ where
  | nil (v) : G.EdgePath v v
  | cons {v w u} : G.EdgeBetween v w → G.EdgePath w u → G.EdgePath v u

abbrev singletonPath (e : G.EdgeBetween u v) := EdgePath.cons e (.nil v)

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

def fold (φ : {u v : V} → G.EdgeBetween u v → A) (comp : A → A → A) (init : A) {v w : V} : G.EdgePath v w → A
  | .nil _ => init
  | .cons e p => comp (φ e) (fold φ comp init p)

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

theorem append_concat {v w w' u : V} (e : EdgeBetween G w' u)(p: EdgePath G v w)(q: EdgePath G w w') :
  p ++ (concat q e) = concat (p ++ q) e := by
  induction p <;> aesop

theorem cons_eq_append_singletonPath {u v w : V} (e : G.EdgeBetween u v) (p : G.EdgePath v w) : 
    EdgePath.cons e p = G.singletonPath e ++ p := rfl

theorem singletonPath_bar (e : G.EdgeBetween u v) : G.singletonPath e.bar = reverse (G.singletonPath e) := rfl

theorem concat_eq_append_edge {v w u : V} (e : G.EdgeBetween w u) (p : G.EdgePath v w) :
    p.concat e = p ++ (cons e (nil u)) := by
  have := concat_append e p (.nil _)
  aesop

theorem append_assoc { v w u u' :  V}
  (p: G.EdgePath v w)(q: G.EdgePath w u)(r: G.EdgePath u u') : 
    (p ++ q) ++ r = p ++ (q ++ r) := by 
    induction p <;> aesop

@[simp] theorem reverse_reverse {v w : V} (p : G.EdgePath v w) : 
  p.reverse.reverse = p := by
  induction p <;> aesop (add norm simp [reverse_cons, reverse_concat])

theorem reverse_append {u v w : V} (p : G.EdgePath u v) (q : G.EdgePath v w) :
    (p ++ q).reverse = q.reverse ++ p.reverse := by
  induction p <;>
    aesop (add norm simp [reverse_cons, concat_eq_append_edge, append_assoc])

@[aesop safe [constructors, cases]]
inductive Reduction {v w : V}:
      G.EdgePath v w →  G.EdgePath v w →  Prop where
  | step (u u' : V)(e : G.EdgeBetween u u') (p₁ : G.EdgePath v u) (p₂ : G.EdgePath u w) : 
      Reduction (p₁ ++ (cons e (cons e.bar p₂))) (p₁ ++ p₂)

def reduced  {v w : V} (p : G.EdgePath v w) : Prop := 
  ∀ p', ¬ Reduction p p'

theorem Reduction.existence {v w : V} (p p' : G.EdgePath v w) : 
  Reduction p p' →
  ∃ u u': V, ∃ e : G.EdgeBetween u u', 
    ∃ p₁ : G.EdgePath v u,
    ∃ p₂ : G.EdgePath u w, 
      p₁ ++ (cons e (cons e.bar p₂)) = p 
| Reduction.step u u' e' p₁ p₂ => by
  use u, u', e', p₁, p₂
  

end EdgePath

open EdgePath

theorem reverse_reduced {v w : V} (p : G.EdgePath v w): reduced p →   reduced p.reverse := by
  intro red rev_targ rev_red
  let ⟨u, u', e, p₁, p₂, eqn⟩   := rev_red.existence
  apply red (reverse p₂ ++ reverse p₁)
  let eqn' := congrArg reverse eqn
  simp [reverse_reverse] at eqn'
  have eqn'' : (reverse p₂) ++ (cons e (cons e.bar (reverse p₁))) =
    p := by
      rw [←eqn', reverse_append]
      simp [reverse_cons]
  rw [←eqn'']
  apply Reduction.step
  
theorem reverse_reduced_iff {v w : V} (p : G.EdgePath v w) :
  reduced p ↔ reduced p.reverse := by
  apply Iff.intro
  · exact reverse_reduced p
  · intro h
    rw [← reverse_reverse p]
    apply reverse_reduced 
    assumption

abbrev PathClass (G: Graph V E) (v w : V)  := 
    Quot <| @Reduction _ _ G v w

abbrev homotopyClass  {v w : V} (p : G.EdgePath v w) :
   PathClass G v w  := 
  Quot.mk _ p

notation "[[" p "]]" => homotopyClass p

attribute [aesop safe apply] Quot.sound

@[simp] theorem append_cons_bar_cons (e : G.EdgeBetween u u') (p₁ : G.EdgePath v u) (p₂ : G.EdgePath u w) :
    [[p₁ ++ (p₂ |>.cons e.bar |>.cons e)]] = [[p₁ ++ p₂]] := by
  have := Reduction.step _ _ e p₁ p₂
  aesop

@[simp] theorem append_cons_cons_bar (e : G.EdgeBetween u' u) (p₁ : G.EdgePath v u) (p₂ : G.EdgePath u w) : 
  [[p₁ ++ (p₂ |>.cons e |>.cons e.bar)]] = [[p₁ ++ p₂]] := by
  have := append_cons_bar_cons e.bar p₁ p₂
  aesop

theorem left_append_step {v w u : V} (a : G.EdgePath v w)  (b₁ b₂ : G.EdgePath w u)  (rel : Reduction  b₁ b₂) : 
   [[a ++ b₁]] = [[a ++ b₂]] := by
    induction rel
    repeat (rw [← append_assoc])
    aesop

theorem right_append_step {v w u : V} (a₁ a₂ : G.EdgePath v w)  (b : G.EdgePath w u) (rel : Reduction  a₁ a₂) : 
    [[a₁ ++ b]] = [[a₂ ++ b]] := by
  aesop (add norm simp [append_assoc])

theorem reverse_step {v w : V} (a₁ a₂ : G.EdgePath v w) (rel : Reduction a₁ a₂) :
    [[a₁.reverse]] = [[a₂.reverse]] := by
  induction rel
  aesop (add norm simp [reverse_append, reverse_cons])

@[simp] theorem reverse_left_inverse {v w : V} 
(p : G.EdgePath v w) : 
    [[p.reverse ++ p]] = [[.nil w]] := by
    induction p <;>
      aesop (add norm simp [reverse_cons, reverse_concat, cons_append])

@[simp] theorem reverse_right_inverse {v w : V} (p : G.EdgePath w v) :
    [[p ++ p.reverse]] = [[.nil w]] := by
  have := reverse_left_inverse p.reverse
  aesop

def EdgePath.toEdgeList {G : Graph V E} {v w : V} (p : EdgePath G v w) : 
  List E := 
  match p with
  | nil _ => []
  | cons e p' =>  e.edge :: p'.toEdgeList

theorem nil_edgeList {G : Graph V E} {v : V}  : 
  (nil v : EdgePath G v v).toEdgeList = [] := rfl

theorem cons_edgeList {G: Graph V E} {v w u: V} (e : EdgeBetween G v w) 
    (p : EdgePath G w u) : 
  (cons e p).toEdgeList = e.edge :: p.toEdgeList := rfl

theorem edgeList_append {G : Graph V E}{v w u : V} (p₁ : EdgePath G v w) (p₂ : EdgePath G w u) :
    (p₁ ++ p₂).toEdgeList = p₁.toEdgeList ++ p₂.toEdgeList := by
    induction p₁ with
    | nil v => 
      simp [nil_edgeList]
    | cons e p' ih =>
      simp [cons_edgeList]
      apply ih

theorem edgeList_concat {G : Graph V E}{v w u : V} (p : EdgePath G v w) (e : EdgeBetween G w u) :
    (concat p e).toEdgeList = List.concat p.toEdgeList e.edge := by
    induction p with
    | nil v => 
      simp [nil_edgeList]
      rw [concat, cons_edgeList, nil_edgeList]
    | cons e p' ih =>
      simp [cons_edgeList, ih]

theorem edgeList_reverse {G : Graph V E}{v w : V} (p : EdgePath G v w):
  p.reverse.toEdgeList  = p.toEdgeList.reverse.map (G.bar) := by
  induction p with
  | nil _ => 
    simp [nil_edgeList]
  | cons e p' ih =>
    simp [cons_edgeList, reverse_cons, edgeList_concat]
    simp [ih, EdgeBetween.bar]

theorem edgeList_reverse' {G : Graph V E}{v w : V} (p : EdgePath G v w):
  p.toEdgeList.reverse = p.reverse.toEdgeList.map (G.bar) := by
  induction p with
  | nil _ => 
    simp [nil_edgeList]
  | cons e p' ih =>
    simp [cons_edgeList, reverse_cons, edgeList_concat]
    simp [ih, EdgeBetween.bar]

@[ext] theorem eq_of_edgeList_eq {G: Graph V E}{v w: V}
  (p₁ p₂ : EdgePath G v w) : p₁.toEdgeList = p₂.toEdgeList → p₁ = p₂ := by
  induction p₁ with
  | nil v =>
    match p₂ with
    | EdgePath.nil v => 
      intro h
      rw [nil_edgeList] at h      
    | EdgePath.cons e₂ p₂  =>
      intro h
      simp [cons_edgeList, nil_edgeList] at h
  | cons e₁ p₁' ih =>
    intro h
    induction p₂ with
    | nil w =>
      simp [cons_edgeList, nil_edgeList] at h
    | cons e₂ p₂'  =>
      simp [cons_edgeList] at h
      have e1t := e₁.target
      have e2t := e₂.target
      rw [h.1] at e1t
      rw [e1t] at e2t
      cases e2t
      congr
      · ext
        exact h.1
      · apply ih
        exact h.2  
        
theorem term_eq_of_edgeList_eq {G: Graph V E}{v₁ v₂ w₁ w₂: V}
  (p₁ : EdgePath G v₁ w₁) (p₂ : EdgePath G v₂ w₂) : p₁.toEdgeList = p₂.toEdgeList → (v₁ = v₂) → (w₁ = w₂)  := by 
  induction p₁ with
  | nil v₁' =>
    match p₂ with
    | EdgePath.nil v => 
      intro h heq
      rw [nil_edgeList] at h      
      exact heq
    | EdgePath.cons e₂ p₂  =>
      intro h
      simp [cons_edgeList, nil_edgeList] at h
  | cons e p₁' ih =>    
    intro h heq
    match p₂ with
    | EdgePath.nil w =>
      simp [cons_edgeList, nil_edgeList] at h
    | EdgePath.cons e₂ p₂' =>
      simp [cons_edgeList] at h
      apply term_eq_of_edgeList_eq p₁' p₂' h.right
      rw [←e₂.target, ←e.target, h.left]

namespace PathClass

@[aesop norm unfold]
protected def id {G : Graph V E} (v : V) : G.PathClass v v :=
  [[.nil v]]

protected def mul {v w u : V} : 
    G.PathClass v w → G.PathClass w u → G.PathClass v u := by
  apply Quot.lift₂ (fun p₁ p₂ ↦ [[ p₁ ++ p₂ ]]) <;>
    aesop (add safe apply [left_append_step, right_append_step])

@[aesop norm unfold]
protected def inv {u v : V} : G.PathClass u v → G.PathClass v u := 
  Quot.lift ([[·.reverse]]) reverse_step

open CategoryTheory

set_option synthInstance.checkSynthOrder false in -- HACK
instance [G : Graph V E] : CategoryStruct V where
  Hom := G.PathClass
  id := PathClass.id
  comp := PathClass.mul

def ind {β : (u ⟶ v) → Prop} : 
   (∀ p : G.EdgePath u v, β [[p]]) → (∀ q : u ⟶ v, β q) :=
  Quot.ind

@[local simp] lemma id_eq_nil (u : V) : 𝟙 u = [[.nil (G := G) u]] := rfl

@[local simp] lemma mul_paths (p : G.EdgePath u v) (p' : G.EdgePath v w) :
  .mul [[p]] [[p']] = [[p ++ p']] := rfl

@[local simp] lemma comp_mul (p : u ⟶ v) (p' : v ⟶ w) :
  p ≫ p' = .mul p p' := rfl

@[simp] protected theorem id_mul  {u v : V} : ∀ p : u ⟶ v, 
  (𝟙 u) ≫ p = p := by
    apply PathClass.ind; aesop

@[simp] protected theorem mul_id  {u v : V} : ∀ p : u ⟶ v,
    p ≫ (𝟙 v) = p := by
  apply PathClass.ind; aesop

@[simp] protected theorem inv_mul {u v : V} : ∀ p : u ⟶ v,
    p.inv ≫ p = 𝟙 v := by
  apply PathClass.ind; aesop

@[simp] protected theorem mul_inv {u v : V} : ∀ p : u ⟶ v,
    p ≫ p.inv = 𝟙 u := by
  apply PathClass.ind; aesop

protected theorem mul_assoc { v w u u' :  V}:
  (p : v ⟶ w) → (q : w ⟶ u) → (r : u ⟶ u') →  
    (p ≫ q) ≫ r = p ≫ (q ≫ r) := by
    apply Quot.ind
    intro a
    apply Quot.ind
    intro b
    apply Quot.ind
    intro c
    simp [append_assoc]

@[simp] lemma nil_eq_id (u : V) : [[Graph.EdgePath.nil (G := G) u]] = 𝟙 u := rfl

@[simp] lemma reverse_class_eq_inv (p : G.EdgePath u v) : [[p.reverse]] = [[p]].inv := rfl

theorem cons_natural{G: Graph V E}{v w u : V} (a : EdgeBetween G v w)  (b₁ b₂ : EdgePath G w u) : [[b₁]] = [[b₂]] → 
   [[cons a  b₁]] = [[cons a b₂]] := by
  intro r
  rw [show cons a b₁ = cons a (nil _) ++ b₁ by rfl, 
      show cons a b₂ = cons a (nil _) ++ b₂ by rfl,
      ← mul_paths, ← mul_paths, r]

theorem concat_natural {G: Graph V E}{v w u : V} (a₁ a₂ : EdgePath G v w)  (b : EdgeBetween G w u) : [[a₁]] = [[a₂]] → 
   [[concat a₁ b]] = [[concat a₂ b]] := by
  intro r
  have: concat a₁  b = a₁ ++ (concat (nil _) b) := by 
    rw [append_concat, append_nil]
  rw [this]
  have: concat a₂  b = a₂ ++ (concat (nil _) b) := by 
    rw [append_concat, append_nil]
  rw [this, ← mul_paths, ← mul_paths, r]

end PathClass

open PathClass CategoryTheory


set_option synthInstance.checkSynthOrder false in -- HACK
@[instance] def FundamentalGroupoid [G : Graph V E] : Groupoid V where
  id_comp := PathClass.id_mul
  comp_id := PathClass.mul_id
  assoc := PathClass.mul_assoc
  inv := PathClass.inv
  inv_comp := PathClass.inv_mul
  comp_inv := PathClass.mul_inv

protected lemma PathClass.inv_eq_inv (p : u ⟶ v) : p.inv = inv p := by
  rw [← Groupoid.inv_eq_inv]; rfl

abbrev π₁ (G: Graph V E) (v : V) := G.PathClass v v

instance : Group (π₁ G v) where
  mul := PathClass.mul
  mul_assoc := PathClass.mul_assoc
  one := .id v
  one_mul := PathClass.id_mul
  mul_one := PathClass.mul_id
  inv := PathClass.inv
  mul_left_inv := PathClass.inv_mul

namespace π₁

variable (G : Graph V E) (base : V)

protected def one_def : 𝟙 base = (1 : G.π₁ base) := rfl

protected def mul_def (p q : base ⟶ base) : p ≫ q = p * q := rfl

protected def inv_def (p : base ⟶ base) : (inv p) = (p : G.π₁ base)⁻¹ := by 
  simp only [Groupoid.vertexGroup_inv, Groupoid.inv_eq_inv]

end π₁

def wedgeCircles (S: Type) : Graph Unit (S × Bool) := {
  ι := fun _ ↦ ()
  bar := fun (e, b) ↦ (e, !b)
  bar_involution := by aesop
  bar_no_fp := by aesop
}

@[ext]
structure PathClassFrom (G : Graph V E) (v : V) where
  τ  : V
  pathClass : PathClass G v τ

end Graph