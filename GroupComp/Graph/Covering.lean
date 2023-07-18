import GroupComp.Graph
import Mathlib.Data.List.Basic

namespace Graph 

open EdgePath PathClass

variable {V : Type u} {E : Type v} 

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
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) {v₂ w₂ : V₂}
    (h : p.vertexMap v₁ = v₂)(e: EdgePath G₂ v₂ w₂) where
  τ : V₁ 
  path: EdgePath G₁ v₁ τ
  lift_term : p.vertexMap τ = w₂
  list_commutes : path.toList.map p.edgeMap = e.toList


def PathLift.pathClass {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    {p : Morphism G₁ G₂}[CoveringMap p] {v₁: V₁} {v₂ w₂ : V₂}
    {h : p.vertexMap v₁ = v₂}{e: EdgePath G₂ v₂ w₂} (l : PathLift p v₁ h e) : PathClassFrom G₁ v₁  := 
      ⟨ l.τ , [[ l.path ]]⟩

def pathLift {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) {v₂ w₂ : V₂}
    (h : p.vertexMap v₁ = v₂)(e: EdgePath G₂ v₂ w₂):
    PathLift p v₁ h e := by
    match e with
    | nil _ => exact ⟨v₁, nil _, h, (by simp [toList])⟩
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
      let ⟨w₁, tail, pf₁, pf₂⟩ := pathLift  p v₁' term_vert b₂
      let edge₁ : EdgeBetween G₁ v₁ v₁' :=
        ⟨e₁, init_vert, rfl⟩
      exact ⟨w₁, cons edge₁ tail, pf₁, by 
        simp [cons_edgeList, pf₂]
        apply p.left_inverse⟩

def EdgePath.lift {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}{v₂ w₂ : V₂}
    (e: EdgePath G₂ v₂ w₂)
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) 
    (h : p.vertexMap v₁ = v₂):
    PathLift p v₁ h e := by
    match e with
    | nil _ => exact ⟨v₁, nil _, h, (by simp [toList])⟩
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
      let ⟨w₁, tail, pf₁, pf₂⟩ := lift b₂  p v₁' term_vert 
      let edge₁ : EdgeBetween G₁ v₁ v₁' :=
        ⟨e₁, init_vert, rfl⟩
      exact ⟨w₁, cons edge₁ tail, pf₁, by 
        simp [cons_edgeList, pf₂]
        apply p.left_inverse⟩


def Morphism.pathMapAux {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (f: Morphism G₁ G₂) (v₁ w₁: V₁) (p: G₁.EdgePath v₁ w₁)
    (v₂ w₂ : V₂)(hv : f.vertexMap v₁ = v₂)(hw : f.vertexMap w₁ = w₂) : 
      {path : G₂.EdgePath v₂ w₂ // path.toList = p.toList.map f.edgeMap} := by 
      match p with
      | nil _ =>
        rw [←hw, hv]
        exact ⟨nil _, by simp [nil_edgeList]⟩
      | cons e p' => 
        rename_i  w₁'' u'
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
    (v₂ w₂ : V₂)(hv : f.vertexMap v₁ = v₂)(hw : f.vertexMap w₁ = w₂) : EdgePath G₂ v₂ w₂ :=
      (pathMapAux f v₁ w₁ p v₂ w₂ hv hw).val

theorem pathMap_toList {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (f: Morphism G₁ G₂) (v₁ w₁: V₁) (p: G₁.EdgePath v₁ w₁)
    (v₂ w₂ : V₂)(hv : f.vertexMap v₁ = v₂)(hw : f.vertexMap w₁ = w₂) :
      (f.pathMap v₁ w₁ p v₂ w₂ hv hw).toList = p.toList.map f.edgeMap := 
      (f.pathMapAux  v₁ w₁ p v₂ w₂ hv hw).property

def EdgePath.map {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}{v₁ w₁: V₁} 
    (p: G₁.EdgePath v₁ w₁)(f: Morphism G₁ G₂)  :=
    (f.pathMapAux v₁ w₁ p (f.vertexMap v₁) (f.vertexMap w₁) rfl rfl).val

theorem map_toList {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (f: Morphism G₁ G₂) {v₁ w₁: V₁} (p: G₁.EdgePath v₁ w₁) :
      (p.map f).toList = p.toList.map f.edgeMap := 
      (f.pathMapAux v₁ w₁ p (f.vertexMap v₁) (f.vertexMap w₁) rfl rfl).property

def asPathLift {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p: Morphism G₁ G₂)[CoveringMap p] {v₁ w₁: V₁} (e: G₁.EdgePath v₁ w₁) :
    PathLift p v₁ rfl   
      (e.map p) := 
    ⟨w₁, e, rfl, by simp [map_toList]⟩

theorem pathLift_commutes {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) (v₂ w₂ : V₂)
    (h : p.vertexMap v₁ = v₂)(e: EdgePath G₂ v₂ w₂) 
    (lift : PathLift p v₁ h e) :
    p.pathMap v₁ lift.τ lift.path v₂ w₂ h lift.lift_term = e := by
      apply eq_of_edgeList_eq
      rw [pathMap_toList, lift.list_commutes]      

theorem lifts_equiv {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂} 
    {v₁ w₁ v₂ w₂ : V₁}
    (p : Morphism G₁ G₂)[CoveringMap p]  
    (e₁ : EdgePath G₁ v₁ w₁) (e₂ : EdgePath G₁ v₂ w₂) (hv: v₁ = v₂) :
    e₁.toList.map p.edgeMap = e₂.toList.map p.edgeMap →
    e₁.toList = e₂.toList := by
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
    (p₁ : PathLift p v₁ h₁ e) → (p₂ : PathLift p v₁ h₂ e) → p₁ = p₂ := by
    intro p₁ p₂
    have eq_edgepath_aux : 
      p₁.path.toList.map p.edgeMap = 
        p₂.path.toList.map p.edgeMap := by
      rw [p₁.list_commutes, p₂.list_commutes]
    have eq_edgepath : p₁.path.toList = p₂.path.toList := by
      apply lifts_equiv p p₁.path p₂.path rfl
      apply eq_edgepath_aux
    have term_eq : p₁.τ = p₂.τ := 
      term_eq_of_edgeList_eq p₁.path p₂.path eq_edgepath rfl
    match p₁, p₂ with
    | ⟨τ₁, path₁, h₁, lc₁⟩, ⟨τ₂, path₂, h₂, lc₂⟩ => 
    have teq : τ₁ = τ₂ := term_eq
    cases teq
    have peq : path₁ = path₂ := by 
      apply eq_of_edgeList_eq
      assumption
    cases peq
    rfl
          

def PathLift.append {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    {p : Morphism G₁ G₂}[CoveringMap p] {v₁: V₁} {v₂ w₂ u₂ : V₂}
    {h : p.vertexMap v₁ = v₂}{e: EdgePath G₂ v₂ w₂}{e': EdgePath G₂ w₂ u₂}
    (lift : PathLift p v₁ h e) 
    (lift' : PathLift p lift.τ  lift.lift_term e') : 
      PathLift p v₁  h (e ++ e') := 
      {τ := lift'.τ, 
        path := lift.path ++ lift'.path, 
        lift_term := lift'.lift_term, 
        list_commutes := by 
          simp [edgeList_append]
          rw [lift.list_commutes, lift'.list_commutes]}
          
theorem pathLift_append {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] {v₁: V₁} {v₂ w₂ u₂ : V₂}
    {h : p.vertexMap v₁ = v₂}{e: EdgePath G₂ v₂ w₂}{e': EdgePath G₂ w₂ u₂}: 
      pathLift p v₁ h (e ++ e') =
        (pathLift p v₁ h e).append 
          (pathLift p (pathLift p v₁ h e).τ  
            (pathLift p v₁ h e).lift_term e') := by
        apply unique_Pathlift 

theorem pathLift_append_tail {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] {v₁: V₁} {v₂ w₂ u₂ : V₂}
    {h : p.vertexMap v₁ = v₂}{e: EdgePath G₂ v₂ w₂}{e': EdgePath G₂ w₂ u₂}: 
      (pathLift p v₁ h (e ++ e')).τ = 
        (pathLift p (pathLift p v₁  h e).τ  
            (pathLift p v₁ h e).lift_term e').τ := by
        simp [pathLift_append]
        rfl

def PathLift.reverse {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] {v₁: V₁} {v₂ w₂ : V₂}
    {h : p.vertexMap v₁ = v₂}{e: EdgePath G₂ v₂ w₂} 
    (lift : PathLift p v₁ h e) : 
      PathLift p lift.τ  lift.lift_term e.reverse := 
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
      pathLift p (pathLift p v₁ h e).τ  
        (pathLift p v₁ h e).lift_term (e.reverse) = 
        (pathLift p v₁ h e).reverse := by
        apply unique_Pathlift

def PathLift.cons_bar_cons {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    {p : Morphism G₁ G₂}[CoveringMap p] {v₁: V₁} {v₂ w₂ w₂' : V₂}
    {h : p.vertexMap v₁ = v₂}{e: EdgeBetween G₂ v₂ w₂'}{e': EdgePath G₂ v₂ w₂}(lift' : PathLift p v₁  h e') : 
      PathLift p v₁ h (cons e (cons e.bar e')) := 
      let edgeLift := p.localSection v₁ e.edge (by rw [h, e.source])
      let edgeBetween : EdgeBetween G₁ v₁ (G₁.τ edgeLift) := 
          ⟨edgeLift, p.section_init _ _ _, rfl⟩ 
          
      {τ := lift'.τ, 
        path := cons edgeBetween (cons edgeBetween.bar lift'.path), 
        lift_term := lift'.lift_term, 
        list_commutes := by 
          simp [cons_edgeList, p.left_inverse, EdgeBetween.bar]
          apply And.intro
          · rw [p.bar_commutes, p.left_inverse]
          · rw [lift'.list_commutes]}


theorem homotopy_step_lift {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    {p : Morphism G₁ G₂}[CoveringMap p] {v₁: V₁} {v₂ w₂ w₂' u₂  : V₂}
    {h : p.vertexMap v₁ = v₂}{η₁: EdgePath G₂ v₂ w₂}{e: EdgeBetween G₂ w₂ w₂'}{η₂: EdgePath G₂ w₂ u₂}:
    (pathLift p v₁  h (η₁ ++ (cons e (cons e.bar η₂)))).pathClass = 
    (pathLift p v₁  h (η₁ ++ η₂)).pathClass := by
  let θ₁ := pathLift p v₁ h η₁
  let w₁ := θ₁.τ
  let hw : p.vertexMap w₁ = w₂ := θ₁.lift_term
  let edgeLift := p.localSection w₁ e.edge (by rw [hw, e.source])
  let e' : EdgeBetween G₁ w₁ (G₁.τ edgeLift) := 
          ⟨edgeLift, p.section_init _ _ _, rfl⟩ 
  let θ₂ := pathLift p w₁ hw η₂
  let liftTailCanc : PathLift p w₁ hw (cons e (cons e.bar η₂)) :=
    {τ := θ₂.τ, 
        path := cons e' (cons e'.bar θ₂.path), 
        lift_term := θ₂.lift_term, 
        list_commutes := by 
          simp [cons_edgeList, p.left_inverse, EdgeBetween.bar]
          apply And.intro
          · rw [p.bar_commutes, p.left_inverse]
          · rw [θ₂.list_commutes]}
  let liftCanc :=
    θ₁.append liftTailCanc
  have splitLift :
    pathLift p v₁ h (η₁ ++ (cons e (cons e.bar η₂))) =
      liftCanc := by
        apply unique_Pathlift
  rw [splitLift]
  have splitLift' :
    pathLift p v₁ h (η₁ ++ η₂) =
      θ₁.append θ₂ := by
        apply unique_Pathlift
  rw [splitLift']
  show (⟨θ₂.τ, [[ liftCanc.path ]]⟩ : PathClassFrom G₁ v₁) = 
    ⟨θ₂.τ, [[ (θ₁.append θ₂).path ]]⟩
  have path1 : liftCanc.path =
    θ₁.path ++ (cons e' (cons e'.bar θ₂.path)) := by
      rfl
  have : [[ liftCanc.path ]] = [[ (θ₁.append θ₂).path ]] := by
    apply Quot.sound
    rw [path1]
    apply Reduction.step
  rw [this]

def homotopyLift {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) {v₂ w₂   : V₂}
    (h : p.vertexMap v₁ = v₂): PathClass G₂ v₂ w₂ → 
    PathClassFrom G₁ v₁ := by
  apply Quot.lift (fun η₂ => (pathLift p v₁ h η₂).pathClass)
  intro η₂ η₂' red
  induction red
  apply homotopy_step_lift

theorem homotopyLift_of_path {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    {p : Morphism G₁ G₂}[CoveringMap p] {v₁: V₁} {v₂ w₂   : V₂}
    {h : p.vertexMap v₁ = v₂} (e : EdgePath G₂ v₂ w₂) :
    homotopyLift p v₁ h [[ e ]] = 
      (pathLift p v₁ h e).pathClass := by
    rfl

def liftClass {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) (v₂ w₂ : V₂)
    (h : p.vertexMap v₁ = v₂)(e: EdgePath G₂ v₂ w₂): 
    PathClassFrom G₁ v₁ :=
  (pathLift p v₁ h e).pathClass

theorem liftClass_eq_of_equiv {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) {v₂ w₂   : V₂}
    (h : p.vertexMap v₁ = v₂) {e₁ e₂ : EdgePath G₂ v₂ w₂} 
    (red : [[ e₁ ]] = [[ e₂ ]]) :
    liftClass p v₁ v₂ w₂ h e₁ = liftClass p v₁ v₂ w₂ h  e₂ := by
    simp [liftClass, ← homotopyLift_of_path]
    congr

def liftTerm {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) {v₂ w₂ : V₂}
    (h : p.vertexMap v₁ = v₂)(e: EdgePath G₂ v₂ w₂) : V₁:=
  (liftClass p v₁ v₂ w₂ h e).τ

theorem liftTerm_eq_of_equiv {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) {v₂ w₂   : V₂}
    (h : p.vertexMap v₁ = v₂) {e₁ e₂ : EdgePath G₂ v₂ w₂} 
    (red : [[ e₁ ]] = [[ e₂ ]]) :
    liftTerm p v₁ h e₁ = liftTerm p v₁ h  e₂ := by
    simp [liftTerm]
    rw [liftClass_eq_of_equiv _ _ _ red]

theorem lift_of_proj {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p: Morphism G₁ G₂)[CoveringMap p] {v₁ w₁: V₁} (e: G₁.EdgePath v₁ w₁):
    pathLift p v₁ rfl (e.map p)  = ⟨w₁, e, rfl, by simp [map_toList]⟩ := by
    apply unique_Pathlift

theorem proj_injective {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p: Morphism G₁ G₂)[CoveringMap p] {v₁ w₁: V₁} 
    (e₁ e₂: G₁.EdgePath v₁ w₁): [[ e₁.map p ]] = [[ e₂.map p ]] → [[ e₁ ]] = [[ e₂ ]] := by
    intro hyp
    let lem := 
      liftClass_eq_of_equiv p v₁ rfl hyp
    simp [liftClass, PathLift.pathClass] at lem
    rw [lift_of_proj] at lem
    rw [lift_of_proj] at lem
    simp at lem
    exact lem

end Graph