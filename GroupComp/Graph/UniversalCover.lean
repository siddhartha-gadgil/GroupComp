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
          
          sorry
    else
    simp [prepReduced_cons_vertex_neq e e' p' c]
    sorry

#check EdgePath.noConfusion