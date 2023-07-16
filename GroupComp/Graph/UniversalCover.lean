import GroupComp.Graph.Covering
import Mathlib
namespace Graph

open EdgePath PathClass

variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

def prepReduced (G : Graph V E) {u v w : V} (e: EdgeBetween G u v) (p : EdgePath G v w) : EdgePath G u w := by
  match p with
  | nil _ => exact cons e (nil v)
  | cons e' p' => 
      rename_i w' w''
      if c:w'' = u then
        cases c
        if e' = e.bar then exact p'
          else exact cons e (cons e' p')
      else
      exact cons e (cons e' p')

theorem prepReduced_nil {G : Graph V E} {u v : V} (e: EdgeBetween G u v) : prepReduced G e (nil v) = cons e (nil v) := by
  simp [prepReduced]

theorem prepReduced_cons_vertex_neq {G : Graph V E} {u v v' w : V} (e: EdgeBetween G u v) (e' : EdgeBetween G v v') (p : EdgePath G v' w) (h : v' ≠ u) : prepReduced G e (cons e' p) = cons e (cons e' p) := by
  simp [prepReduced, h]
    
theorem prepReduced_cons_edge_neq {G : Graph V E} {u v w : V} 
  {e: EdgeBetween G u v} {e' : EdgeBetween G v u} (p : EdgePath G u w)
  (h : e' ≠ e.bar) : 
    prepReduced G e (cons e' p) = cons e (cons e' p) := by 
  simp [prepReduced, h]
  
theorem prepReduced_cons_edge_eq {G : Graph V E} {u v w : V}
  {e: EdgeBetween G u v} {e' : EdgeBetween G v u} (p : EdgePath G u w)
  (h : e' = e.bar) : 
    prepReduced G e (cons e' p) = p := by 
  simp [prepReduced, h]

theorem prepend_cases {G : Graph V E} {u v w : V} (e: EdgeBetween G u v) (p : EdgePath G v w) :
  (prepReduced G e p) = cons e p ∨ (
    ∃ t : EdgePath G u w, p = cons e.bar t ∧  (prepReduced G e p = t)
  ) 
   := by
  match p with
  | nil _ => 
    simp only [prepReduced_nil, false_and, exists_false, or_false]
  | cons e' p' =>
    rename_i w' w''
    if c:w'' = u then
      cases c
      if c':e' = e.bar 
        then
          simp [prepReduced_cons_edge_eq p' c']
          simp only [c', or_true]          
        else
          simp [prepReduced_cons_edge_neq p' c']
    else
      simp only [prepReduced_cons_vertex_neq e e' p' c, cons.injEq, exists_eq_right', true_or]
      


theorem tail_reducible_of_split {G : Graph V E} {u v w v' w': V} {e : EdgeBetween G u v} {p : EdgePath G v w}
    {ph: EdgeBetween G u v'}{pt : EdgePath G v' w'}
    {e' : EdgeBetween G w' u'}{p₂ : EdgePath G w' w} 
    (hyp : cons e p = (cons ph pt) ++ (cons e' (cons e'.bar p₂))) :
    ¬ reduced p := by
  rw [cons_append] at hyp
  let lhyp := congrArg EdgePath.toEdgeList hyp
  simp only [cons_edgeList, edgeList_append, EdgeBetween.bar_def, List.cons.injEq] at lhyp 
  have : v' = v := by
    rw [← e.target, ←ph.target]
    symm
    apply congrArg G.τ lhyp.left
  cases this
  have : p = pt ++ (cons e' (cons  e'.bar  p₂)) := by
    apply eq_of_edgeList_eq
    simp [cons_edgeList, edgeList_append]
    exact lhyp.2
  exact not_reduced_of_split this
  

theorem reduced_prepReduced (G : Graph V E) {u v w : V} (e: EdgeBetween G u v) (p : EdgePath G v w) (hyp : reduced p):
  reduced (prepReduced G e p) := by
  match p with
  | nil _ => 
    simp [prepReduced_nil]
    intro p' red'
    let ⟨u, u', e, p₁, p₂, eqn⟩   := red'.existence
    cases p₁ with
    | nil _ => 
      rw [nil_append] at eqn
      let leqn := congrArg EdgePath.toEdgeList eqn
      simp [cons_edgeList, nil_edgeList] at leqn      
    | cons h t => 
      rw [cons_append] at eqn
      let leqn := congrArg EdgePath.toEdgeList eqn
      simp [cons_edgeList, nil_edgeList, edgeList_append] at leqn 
  | cons e' p' => 
    rename_i w' w''
    if c:w'' = u then
      cases c
      if c':e' = e.bar 
        then 
          simp [prepReduced_cons_edge_eq p' c']
          intro p'' red'
          let ⟨u, u', e, p₁, p₂, eqn⟩   := red'.existence
          rw [←eqn, ← cons_append] at hyp
          let red := hyp <| cons e' p₁ ++ p₂
          apply red
          apply Reduction.step
        else 
          simp [prepReduced_cons_edge_neq p' c']
          intro p'' red'
          let ⟨u, u', e, p₁, p₂, eqn⟩   := red'.existence
          match p₁ with
          | nil _ => 
            rw [nil_append] at eqn
            let leqn := congrArg EdgePath.toEdgeList eqn
            simp [cons_edgeList, nil_edgeList, edgeList_append] at leqn
            rename_i e''
            have : e' = e''.bar := by
              ext
              rw [EdgeBetween.bar_def]
              rw [← leqn.1, leqn.2.1]
            contradiction
          | cons ph pt =>
            symm at eqn
            let tred : ¬ reduced (cons e' p') := 
              tail_reducible_of_split eqn
            contradiction
    else
      simp [prepReduced_cons_vertex_neq e e' p' c]
      intro p'' red'
      let ⟨u, u', e, p₁, p₂, eqn⟩   := red'.existence
      match p₁ with
          | nil _ => 
            rw [nil_append] at eqn
            let leqn := congrArg EdgePath.toEdgeList eqn
            simp [cons_edgeList, nil_edgeList, edgeList_append] at leqn
            rename_i u'' e''
            apply c
            rw [← e.source, ← e'.target, ← G.ι_bar, ← leqn.2.1, bar_involution]
          | cons ph pt =>
            symm at eqn
            let tred : ¬ reduced (cons e' p') := 
              tail_reducible_of_split eqn
            contradiction

theorem cancelling_steps_prepReduced {G : Graph V E} {u v w : V} (e: EdgeBetween G u v) (p : EdgePath G v w) (hyp : reduced p):
  prepReduced G e.bar (prepReduced G e p) = p := by
  cases prepend_cases e p with
  | inl h => 
      rw [h]
      apply prepReduced_cons_edge_eq
      simp [bar_involution]
  | inr h => 
      let ⟨t, h₁, h₂⟩ := h
      rw[h₂, h₁]
      cases prepend_cases e.bar t with
      | inl h' => 
        assumption
      | inr h' => 
        let ⟨t', h₁', h₂'⟩ := h'
        rw [h₂', h₁']
        rw [h₁, h₁'] at hyp
        simp [bar_involution] at *
        have split :
                  cons e.bar (cons e t') = 
                    (nil v : EdgePath G v v) ++ 
                      cons e.bar (cons e.bar.bar t') := by
                    simp [nil_append]
        have :¬ reduced (cons e.bar (cons e t')) := by
          apply not_reduced_of_split split
        contradiction

theorem prepend_changes_parity {G : Graph V E} {u v w : V} (e: EdgeBetween G u v) (p : EdgePath G v w) :
  Even ((prepReduced G e p).toEdgeList.length) ↔ ¬ Even (p.toEdgeList.length) := by
  cases prepend_cases e p with
  | inl h => 
    rw [h]
    simp only [cons_edgeList, List.length_cons]
    apply Nat.even_add_one
  | inr h =>
    let ⟨t, h₁, h₂⟩ := h
    rw [h₂, h₁]
    simp  [cons_edgeList, List.length_cons, Nat.even_add_one]
  
def reducedConcat {G : Graph V E} {v w u : V}  (p : EdgePath G v w) (e: EdgeBetween G w u) : 
  EdgePath G v u := 
  reverse <| prepReduced G e.bar (reverse p)

infixl:65 ":+" => reducedConcat

theorem reducedConcat_reduced {G : Graph V E} {v w u : V}  (p : EdgePath G v w) (e: EdgeBetween G w u) (hyp : reduced p) :
  reduced (p :+ e) := by
  simp only [reducedConcat]
  apply reverse_reduced
  apply reduced_prepReduced
  apply reverse_reduced
  apply hyp

theorem reducedConcat_cancel_pair {G : Graph V E} {v w u : V}  (p : EdgePath G v w) (e: EdgeBetween G w u) (hyp : reduced p) :
    p :+ e :+ e.bar = p := by
  have hyp' :=  reverse_reduced p hyp
  simp only [reducedConcat, EdgeBetween.bar_involution, reverse_reverse]
  let lm : 
    prepReduced G e.bar.bar (prepReduced G (EdgeBetween.bar e) (reverse p)) 
      = reverse p :=
    by
      apply cancelling_steps_prepReduced
      assumption
  simp at lm
  rw [lm, reverse_reverse]

theorem concat_parity {G : Graph V E} {v w u : V}  (p : EdgePath G v w) (e: EdgeBetween G w u)  :
  Even ((p :+ e).toEdgeList.length) ↔ ¬ Even (p.toEdgeList.length) := by
  simp  [reducedConcat, edgeList_reverse]
  rw [prepend_changes_parity e.bar (reverse p)]
  simp [edgeList_reverse]

/-!
## Construction of the Universal covering

We construct the universal cover given a baspoint `x₀` with

* Vertices: reduced edge paths starting at `x₀`
* Edges: reduces edge paths starting at `x₀` followed by an edge.

The non-trivial part is the construction of the `bar` map. The initial vertex should be the terminal vertex of the given edge. This is obtained by reduced concat, using the fact that the result is reduced. The other result is used to show that the `bar` map is an involution.
-/

namespace UniversalCover

variable (G: Graph V E) (x₀ : V)

@[ext]
structure Vert where
  τ : V
  p : EdgePath G x₀ τ
  is_reduced : @reduced V E G x₀ τ p

@[ext]
structure Edge where
  τ₀ : V
  τ₁ : V
  nxt: EdgeBetween G τ₀ τ₁
  p : EdgePath G x₀ τ₀
  is_reduced : reduced p
  
  
  
namespace Edge

def initial (e : Edge G x₀) : Vert G x₀ := 
  ⟨e.τ₀, e.p, e.is_reduced⟩

def terminal (e : Edge G x₀) : Vert G x₀ :=
  ⟨e.τ₁, e.p :+ e.nxt, reducedConcat_reduced e.p e.nxt e.is_reduced⟩

def bar (e : Edge G x₀) : Edge G x₀ :=
  ⟨e.τ₁, e.τ₀, e.nxt.bar, e.p :+ e.nxt,  reducedConcat_reduced e.p e.nxt e.is_reduced⟩

theorem bar_involution (e : Edge G x₀) : 
    bar G x₀ (bar G x₀ e) = e := by
  simp only [bar, EdgeBetween.bar_involution]
  ext
  · rfl
  · rfl
  · rfl  
  · simp only [Eq.ndrec, id_eq, heq_eq_eq]
    apply reducedConcat_cancel_pair
    exact e.is_reduced

def edgeList (e : Edge G x₀) : List E := 
  e.p.toEdgeList

theorem bar_neq_self (e: Edge G x₀) :
  e ≠ bar G x₀ e := by
  intro contra
  have : e.p.toEdgeList.length =  (bar G x₀ e).p.toEdgeList.length 
     := by
      rw [← contra]
  simp [bar, Edge.p] at this
  let h' := concat_parity e.p e.nxt 
  rw [this] at h' 
  symm at h'
  let h'' := not_iff_self  h'
  assumption

def Guniv : Graph (Vert G x₀) (Edge G x₀) where
  ι := initial G x₀
  bar := bar G x₀
  bar_involution := bar_involution G x₀
  bar_no_fp := bar_neq_self G x₀

def proj : Morphism (Guniv G x₀) G where
  vertexMap := Vert.τ
  edgeMap := fun e ↦ e.nxt.edge 
  commutes := by
    intro e
    match e with
    | ⟨τ₀, τ₁, nxt, _, _⟩ => 
      show τ₀ = G.ι nxt.edge
      rw [nxt.source]
  bar_commutes := by
    intro e
    rfl
      
lemma shift_heq (τ₀ τ₁ τ₂ : V)(edge : E)(source : G.ι edge = τ₀)
    (target₁ : G.τ edge = τ₁)(target₂ : G.τ edge = τ₂):
    HEq (⟨edge, source, target₁⟩ : EdgeBetween G τ₀ τ₁)
      (⟨edge, source, target₂⟩ : EdgeBetween G τ₀ τ₂) := by
    induction target₁
    induction target₂
    rfl

instance : CoveringMap (proj G x₀) where
  localSection := 
    fun v₁ e h ↦
      ⟨v₁.τ, G.τ e, ⟨e, Eq.symm h, rfl⟩, v₁.p, v₁.is_reduced⟩
  section_init := by
    intro v₁ e h
    match v₁ with
    | ⟨τ, p, red⟩ =>
      have h' : τ = G.ι e := h
      cases h'
      rfl
  left_inverse := by
    intro v₁ e h
    match v₁ with
    | ⟨τ, p, red⟩ =>
      have h' : τ = G.ι e := h
      cases h'
      rfl 
  right_inverse := by
    intro v₁ e₁ h₁   
    have : (proj G x₀).edgeMap e₁ = e₁.nxt.edge := rfl
    let l := e₁.nxt.target
    rw [← this] at l
    match e₁ with
    | ⟨τ₀, τ₁, nxt, p, red⟩ =>
      cases h₁ 
      show _ = (⟨τ₀, τ₁, nxt, p, red⟩ : Edge G x₀)
      ext
      · rfl
      · rw [← l]
      · show HEq 
          (⟨nxt.edge, nxt.source , rfl⟩  : EdgeBetween G τ₀ (G.τ nxt.edge)) nxt
        apply shift_heq
      · rfl 
end Edge
