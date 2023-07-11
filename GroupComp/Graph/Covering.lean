import GroupComp.Graph

namespace Graph 

open EdgePath PathClass

variable {V : Type u} {E : Type v} (G : Graph V E)
variable {u v w : V}
variable {G} (e : G.EdgeBetween v w)

@[ext] structure Morphism (G₁ : Graph V₁ E₁) (G₂ : Graph V₂ E₂) where
  vertexMap : V₁ → V₂
  edgeMap : E₁ → E₂
  commutes : ∀ (e : E₁),  vertexMap (G₁.ι e) = G₂.ι (edgeMap e) 
  bar_commutes : ∀ (e : E₁), edgeMap (G₁.bar e) = G₂.bar (edgeMap e)

theorem morphism_init_commutes {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂} 
    (f: Morphism G₁ G₂) : 
      ∀ (e : E₁), f.vertexMap (G₁.ι e) = G₂.ι (f.edgeMap e)  := by
  intro e
  exact f.commutes e

theorem morphism_bar_commutes {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂} 
    (f: Morphism G₁ G₂) : 
      ∀ (e : E₁), f.edgeMap (G₁.bar e) = G₂.bar (f.edgeMap e) := by
  intro e
  exact f.bar_commutes e

theorem morphism_term_commutes {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂} 
    (f: Morphism G₁ G₂) : 
      ∀ (e : E₁), G₂.τ (f.edgeMap e) = f.vertexMap (G₁.τ e) := by
  intro e
  rw [Graph.τ, Graph.τ, ←morphism_bar_commutes, ←morphism_init_commutes]



class CoveringMap {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂} 
      (p: Morphism G₁ G₂)  where
  localSection : (v₁ : V₁) → (e :E₂) → 
      p.vertexMap v₁ = G₂.ι e   → E₁
  section_init : (v₁ : V₁) → (e₂ : E₂) → 
    (h : p.vertexMap v₁ = G₂.ι e₂) → 
    G₁.ι (localSection v₁ e₂ h) = v₁ 
  left_inverse : (v₁ : V₁) → (e₂ :E₂) → 
    (h : p.vertexMap v₁ = G₂.ι e₂) → 
    p.edgeMap (localSection v₁ e₂ h) = e₂
  right_inverse : (v₁ : V₁) → (e₁ : E₁) →
    (h : v₁ = G₁.ι e₁) →  
    localSection v₁ (p.edgeMap e₁) (by rw [← p.commutes, h]) = 
      e₁ 

namespace Morphism

def localSection {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂} 
      (p: Morphism G₁ G₂) [CoveringMap p] (v₁ : V₁) (e₂ : E₂) 
      (h : p.vertexMap v₁ = G₂.ι e₂) : E₁ := 
        CoveringMap.localSection v₁ e₂ h

def section_init {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
      (p: Morphism G₁ G₂) [CoveringMap p] (v₁ : V₁) (e₂ : E₂) 
      (h : p.vertexMap v₁ = G₂.ι e₂) : 
      G₁.ι (localSection p v₁ e₂ h) = v₁ := 
        CoveringMap.section_init v₁ e₂ h

theorem left_inverse {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
      (p: Morphism G₁ G₂) [CoveringMap p] (v₁ : V₁) (e₂ : E₂) 
      (h : p.vertexMap v₁ = G₂.ι e₂) : 
      p.edgeMap (localSection p v₁ e₂ h) = e₂ := 
        CoveringMap.left_inverse v₁ e₂ h


theorem right_inverse {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
      (p: Morphism G₁ G₂) [CoveringMap p] (v₁ : V₁) (e₁ : E₁) 
      (h : v₁ = G₁.ι e₁) : 
      localSection p v₁ (p.edgeMap e₁) (by rw [← p.commutes, h]) = 
        e₁ := 
          CoveringMap.right_inverse v₁ e₁ h

end Morphism

@[ext]
structure PathLift {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) (v₂ w₂ : V₂)
    (h : p.vertexMap v₁ = v₂)(e: EdgePath G₂ v₂ w₂) where
  τ : V₁ 
  path: EdgePath G₁ v₁ τ
  lift_term : p.vertexMap τ = w₂
  list_commutes : path.toEdgeList.map p.edgeMap = e.toEdgeList

def pathLift {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) (v₂ w₂ : V₂)
    (h : p.vertexMap v₁ = v₂)(e: EdgePath G₂ v₂ w₂):
    PathLift p v₁ v₂ w₂ h e := by
    match e with
    | nil _ => exact ⟨v₁, nil _, h, (by simp [toEdgeList])⟩
    | cons e₂ b₂ =>
      rename_i w₂' w₂''
      let e₁ := p.localSection v₁ e₂.edge (by rw [h, e₂.source]) 
        -- lift of the edge
      let v₁' := G₁.τ e₁ -- the final vertex of the lift
      have init_vert : G₁.ι e₁ = v₁ := by apply p.section_init
      have term_vert : p.vertexMap (G₁.τ e₁) = w₂'' := by
        rw [← e₂.target]
        rw [←morphism_term_commutes ]
        congr
        apply p.left_inverse
      let ⟨w₁, tail, pf₁, pf₂⟩ := pathLift  p v₁' w₂'' w₂ term_vert b₂
      let edge₁ : EdgeBetween G₁ v₁ v₁' :=
        ⟨e₁, init_vert, rfl⟩
      exact ⟨w₁, cons edge₁ tail, pf₁, by 
        simp [cons_edgeList, pf₂]
        apply p.left_inverse⟩

def Morphism.pathMapAux {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (f: Morphism G₁ G₂) (v₁ w₁: V₁) (p: G₁.EdgePath v₁ w₁)
    (v₂ w₂ : V₂)(hv : f.vertexMap v₁ = v₂)(hw : f.vertexMap w₁ = w₂) : 
      {path : G₂.EdgePath v₂ w₂ // path.toEdgeList = p.toEdgeList.map f.edgeMap} := by 
      match p with
      | nil _ =>
        rw [←hw, hv]
        exact ⟨nil _, by simp [nil_edgeList]⟩
      | cons e p' => 
        rename_i w₁' w₁'' u'
        let e₁ := f.edgeMap e.edge
        let init_vert : G₂.ι e₁ = v₂ := by
          rw [←hv, ←e.source, ←morphism_init_commutes] 
        let term_vert : G₂.τ e₁ = f.vertexMap u' := by
          rw [morphism_term_commutes, e.target]
        let edge₂ : EdgeBetween G₂ v₂ (f.vertexMap u') :=
          ⟨e₁, init_vert, term_vert⟩
        let ⟨tail, ih⟩ := pathMapAux f u' w₁ p' (f.vertexMap u') w₂ rfl hw
        exact ⟨cons edge₂ tail, by simp [cons_edgeList, ih]⟩ 

def Morphism.pathMap {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (f: Morphism G₁ G₂) (v₁ w₁: V₁) (p: G₁.EdgePath v₁ w₁)
    (v₂ w₂ : V₂)(hv : f.vertexMap v₁ = v₂)(hw : f.vertexMap w₁ = w₂) :=
      (pathMapAux f v₁ w₁ p v₂ w₂ hv hw).val

theorem pathMap_toList {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (f: Morphism G₁ G₂) (v₁ w₁: V₁) (p: G₁.EdgePath v₁ w₁)
    (v₂ w₂ : V₂)(hv : f.vertexMap v₁ = v₂)(hw : f.vertexMap w₁ = w₂) :
      (f.pathMap v₁ w₁ p v₂ w₂ hv hw).toEdgeList = p.toEdgeList.map f.edgeMap := 
      (f.pathMapAux  v₁ w₁ p v₂ w₂ hv hw).property


theorem pathLift_commutes {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) (v₂ w₂ : V₂)
    (h : p.vertexMap v₁ = v₂)(e: EdgePath G₂ v₂ w₂) 
    (lift : PathLift p v₁ v₂ w₂ h e) :
    p.pathMap v₁ lift.τ lift.path v₂ w₂ h lift.lift_term = e := by
      apply eq_of_edgeList_eq
      rw [pathMap_toList, lift.list_commutes]      

theorem lifts_equiv {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂} 
    {v₁ w₁ v₂ w₂ : V₁}
    (p : Morphism G₁ G₂)[CoveringMap p]  
    (e₁ : EdgePath G₁ v₁ w₁) (e₂ : EdgePath G₁ v₂ w₂) (hv: v₁ = v₂) :
    e₁.toEdgeList.map p.edgeMap = e₂.toEdgeList.map p.edgeMap →
    e₁.toEdgeList = e₂.toEdgeList := by
    intro hyp
    match e₁ with
    | nil v => 
      simp [nil_edgeList] at hyp
      simp [nil_edgeList]
      symm at hyp
      rw [List.map_eq_nil] at hyp
      symm
      exact hyp
    | cons edg₁ p₁' => 
      match e₂, hv with
      | nil v, _ => 
        simp [nil_edgeList] at hyp
      | cons edg₂ p₂', rfl => 
        simp [cons_edgeList] at *
        let ⟨h₁, h₂⟩ := hyp
        have edg_eq : edg₁.edge = edg₂.edge := by 
          let eq₁ := p.right_inverse v₁ edg₁.edge (Eq.symm edg₁.source)
          let eq₂ := p.right_inverse v₁ edg₂.edge (Eq.symm edg₂.source)
          rw [← eq₁, ← eq₂]
          congr
        simp [edg_eq] 
        apply lifts_equiv p p₁' p₂' 
        · rw [← edg₁.target, ← edg₂.target, edg_eq]
        · exact h₂

theorem unique_Pathlift {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] {v₁: V₁} {v₂ w₂ : V₂}
    {h₁ h₂ : p.vertexMap v₁ = v₂}{e: EdgePath G₂ v₂ w₂} :
    (p₁ : PathLift p v₁ v₂ w₂ h₁ e) → (p₂ : PathLift p v₁ v₂ w₂ h₂ e) → p₁ = p₂ := by
    intro p₁ p₂
    have eq_edgepath_aux : 
      p₁.path.toEdgeList.map p.edgeMap = 
        p₂.path.toEdgeList.map p.edgeMap := by
      rw [p₁.list_commutes, p₂.list_commutes]
    have eq_edgepath : p₁.path.toEdgeList = p₂.path.toEdgeList := by
      apply lifts_equiv p p₁.path p₂.path rfl
      apply eq_edgepath_aux
    have term_eq : p₁.τ = p₂.τ := 
      term_eq_of_edgeList_eq p₁.path p₂.path eq_edgepath rfl
    match p₁, p₂ with
    | ⟨τ₁, path₁, h₁, lc₁⟩, ⟨τ₂, path₂, h₂, lc₂⟩ => 
      simp [term_eq] at h₂
      have teq : τ₁ = τ₂ := term_eq
      match τ₁, path₁, h₁, lc₁, τ₂, path₂, h₂, lc₂, teq with
      | τ, path₁, h₁, lc₁, _, path₂, h₂, lc₂, rfl => 
        have peq : path₁ = path₂ := by 
          apply eq_of_edgeList_eq
          assumption
        match path₁, h₁, lc₁, path₂, h₂, lc₂, peq with
        | _, _, _, _, _, _, rfl => rfl
          

def PathLift.append {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    {p : Morphism G₁ G₂}[CoveringMap p] {v₁: V₁} {v₂ w₂ u₂ : V₂}
    {h : p.vertexMap v₁ = v₂}{e: EdgePath G₂ v₂ w₂}{e': EdgePath G₂ w₂ u₂}
    (lift : PathLift p v₁ v₂ w₂ h e) 
    (lift' : PathLift p lift.τ w₂ u₂ lift.lift_term e') : 
      PathLift p v₁ v₂ u₂ h (e ++ e') := 
      {τ := lift'.τ, 
        path := lift.path ++ lift'.path, 
        lift_term := lift'.lift_term, 
        list_commutes := by 
          simp [edgeList_append]
          rw [lift.list_commutes, lift'.list_commutes]}
          
theorem pathLift_lift_append {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] {v₁: V₁} {v₂ w₂ u₂ : V₂}
    {h : p.vertexMap v₁ = v₂}{e: EdgePath G₂ v₂ w₂}{e': EdgePath G₂ w₂ u₂}: 
      pathLift p v₁ v₂ u₂ h (e ++ e') =
        (pathLift p v₁ v₂ w₂ h e).append 
          (pathLift p (pathLift p v₁ v₂ w₂ h e).τ w₂ u₂ 
            (pathLift p v₁ v₂ w₂ h e).lift_term e') := by
        apply unique_Pathlift 

def PathLift.reverse {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] {v₁: V₁} {v₂ w₂ : V₂}
    {h : p.vertexMap v₁ = v₂}{e: EdgePath G₂ v₂ w₂} 
    (lift : PathLift p v₁ v₂ w₂ h e) : 
      PathLift p lift.τ w₂ v₂ lift.lift_term e.reverse := 
      {τ := v₁, 
        path := lift.path.reverse, 
        lift_term := h, 
        list_commutes := by 
          simp [edgeList_reverse]
          rw [← lift.list_commutes]
          simp [List.map_reverse]
          congr
          funext edge
          show p.edgeMap (G₁.bar edge) = G₂.bar (p.edgeMap edge)
          rw [morphism_bar_commutes]}

theorem pathLift_reverse {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] {v₁: V₁} {v₂ w₂ : V₂}
    {h : p.vertexMap v₁ = v₂}{e: EdgePath G₂ v₂ w₂}: 
      pathLift p (pathLift p v₁ v₂ w₂ h e).τ w₂ v₂ 
        (pathLift p v₁ v₂ w₂ h e).lift_term (e.reverse) = 
        (pathLift p v₁ v₂ w₂ h e).reverse := by
        apply unique_Pathlift

end Graph