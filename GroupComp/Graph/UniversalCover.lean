import GroupComp.Graph.Covering

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
  match p with
  | nil _ => 
    simp [prepReduced_nil, prepReduced_cons_edge_eq]
  | cons e' p' => 
    rename_i w' w''
    if c:w'' = u then
      cases c
      if c':e' = e.bar 
        then 
          simp [prepReduced_cons_edge_eq p' c']
          match p' with
          | nil _ => 
            simp [prepReduced_nil, prepReduced_cons_edge_eq, c']
          | cons e'' p'' =>
            rename_i w₁ w₂
            if c₁: w₂ = v then
              cases c₁
              if c₂ : e'' = e.bar.bar then
                simp at c₂
                rw [c₂, c'] at hyp
                rw [c₂, c']
                have split :
                  cons e.bar (cons e p'') = 
                    (nil v : EdgePath G v v) ++ 
                      cons e.bar (cons e.bar.bar p'') := by
                    simp [nil_append]
                have :¬ reduced (cons e.bar (cons e p'')) := by
                  apply not_reduced_of_split split
                contradiction
              else 
                simp [prepReduced_cons_edge_neq p'' c₂]
                rw [c']
            else
              simp [
                prepReduced_cons_vertex_neq e.bar e'' p'' c₁]
              rw [c']
        else 
          simp [prepReduced_cons_edge_neq p' c', 
          prepReduced_cons_edge_eq]
    else
      simp [prepReduced_cons_vertex_neq e e' p' c, prepReduced_cons_edge_eq]

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
structure Vert' where
  τ : V
  p : EdgePath G x₀ τ
  

@[ext]
structure Edge' where
  τ₀ : V
  τ₁ : V
  nxt: EdgeBetween G τ₀ τ₁
  p : EdgePath G x₀ τ₀

abbrev Vert := {v: Vert' G x₀ // reduced v.p}
abbrev Edge := {e: Edge' G x₀ // reduced e.p}
  
  
namespace Edge

def initial (e : Edge G x₀) : Vert G x₀ := 
  ⟨⟨e.val.τ₀, e.val.p⟩, e.property⟩

def terminal (e : Edge G x₀) : Vert G x₀ :=
  ⟨⟨e.val.τ₁, e.val.p :+ e.val.nxt⟩,
  reducedConcat_reduced e.val.p e.val.nxt e.property⟩

def bar (e : Edge G x₀) : Edge G x₀ :=
  ⟨⟨e.val.τ₁, e.val.τ₀, e.val.nxt.bar, e.val.p :+ e.val.nxt⟩,
  reducedConcat_reduced e.val.p e.val.nxt e.property⟩

theorem bar_involution (e : Edge G x₀) : 
    bar G x₀ (bar G x₀ e) = e := by
  apply Subtype.eq
  simp only [bar, EdgeBetween.bar_involution]  
  ext
  · rfl
  · rfl
  · rfl  
  · simp [reducedConcat_cancel_pair, e.property]

end Edge