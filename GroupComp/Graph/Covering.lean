import GroupComp.Graph
import Mathlib.Data.List.Basic

namespace Graph 

open EdgePath PathClass

variable {V : Type u} {E : Type v} 

@[ext] structure Morphism (G₁ : Graph V₁ E₁) (G₂ : Graph V₂ E₂) where
  mapV : V₁ → V₂
  mapE : E₁ → E₂
  mapV_init : ∀ (e : E₁),  mapV (G₁.ι e) = G₂.ι (mapE e) 
  mapE_bar : ∀ (e : E₁), mapE (G₁.bar e) = G₂.bar (mapE e)

theorem mapV_init {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂} 
    (f: Morphism G₁ G₂) : 
      ∀ (e : E₁), f.mapV (G₁.ι e) = G₂.ι (f.mapE e)  := by
  intro e
  exact f.mapV_init e

theorem mapE_bar {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂} 
    (f: Morphism G₁ G₂) : 
      ∀ (e : E₁), f.mapE (G₁.bar e) = G₂.bar (f.mapE e) := by
  intro e
  exact f.mapE_bar e

theorem mapV_term {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂} 
    (f: Morphism G₁ G₂) : 
      ∀ (e : E₁), f.mapV (G₁.τ e)=  G₂.τ (f.mapE e)  := by
  intro e
  rw [Graph.τ, Graph.τ, ←mapE_bar, ←mapV_init]




class CoveringMap {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂} 
      (p: Morphism G₁ G₂)  where
  localSection : (v₁ : V₁) → (e :E₂) → 
      p.mapV v₁ = G₂.ι e   → E₁
  init_localSection : (v₁ : V₁) → (e₂ : E₂) → 
    (h : p.mapV v₁ = G₂.ι e₂) → 
    G₁.ι (localSection v₁ e₂ h) = v₁ 
  mapE_localSection : (v₁ : V₁) → (e₂ :E₂) → 
    (h : p.mapV v₁ = G₂.ι e₂) → 
    p.mapE (localSection v₁ e₂ h) = e₂
  localSection_mapE : (v₁ : V₁) → (e₁ : E₁) →
    (h : v₁ = G₁.ι e₁) →  
    localSection v₁ (p.mapE e₁) (by rw [← p.mapV_init, h]) = 
      e₁ 

namespace Morphism

def localSection {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂} 
      (p: Morphism G₁ G₂) [CoveringMap p] (v₁ : V₁) (e₂ : E₂) 
      (h : p.mapV v₁ = G₂.ι e₂) : E₁ := 
        CoveringMap.localSection v₁ e₂ h

theorem init_localSection {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
      (p: Morphism G₁ G₂) [CoveringMap p] (v₁ : V₁) (e₂ : E₂) 
      (h : p.mapV v₁ = G₂.ι e₂) : 
      G₁.ι (localSection p v₁ e₂ h) = v₁ := 
        CoveringMap.init_localSection v₁ e₂ h

theorem mapE_localSection {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
      (p: Morphism G₁ G₂) [CoveringMap p] (v₁ : V₁) (e₂ : E₂) 
      (h : p.mapV v₁ = G₂.ι e₂) : 
      p.mapE (localSection p v₁ e₂ h) = e₂ := 
        CoveringMap.mapE_localSection v₁ e₂ h


theorem localSection_mapE {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
      (p: Morphism G₁ G₂) [CoveringMap p] (v₁ : V₁) (e₁ : E₁) 
      (h : v₁ = G₁.ι e₁) : 
      localSection p v₁ (p.mapE e₁) (by rw [← p.mapV_init, h]) = 
        e₁ := 
          CoveringMap.localSection_mapE v₁ e₁ h

end Morphism

@[ext]
structure PathLift {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) {v₂ w₂ : V₂}
    (h : p.mapV v₁ = v₂)(e: EdgePath G₂ v₂ w₂) where
  τ : V₁ 
  path: EdgePath G₁ v₁ τ
  lift_terminal : p.mapV τ = w₂
  list_commutes : path.toList.map p.mapE = e.toList


def PathLift.pathClass {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    {p : Morphism G₁ G₂}[CoveringMap p] {v₁: V₁} {v₂ w₂ : V₂}
    {h : p.mapV v₁ = v₂}{e: EdgePath G₂ v₂ w₂} (l : PathLift p v₁ h e) : PathClassFrom G₁ v₁  := 
      ⟨ l.τ , [[ l.path ]]⟩

def EdgePath.lift {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}{v₂ w₂ : V₂}
    (e: EdgePath G₂ v₂ w₂)
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) 
    (h : p.mapV v₁ = v₂):
    PathLift p v₁ h e := by
    match e with
    | nil _ => exact ⟨v₁, nil _, h, (by simp [toList])⟩
    | cons e₂ b₂ =>
      rename_i w₂' w₂''
      let e₁ := p.localSection v₁ e₂.edge (by rw [h, e₂.source]) 
        -- lift of the edge
      let v₁' := G₁.τ e₁ -- the final vertex of the lift
      have init_vert : G₁.ι e₁ = v₁ := by apply p.init_localSection
      have term_vert : p.mapV (G₁.τ e₁) = w₂'' := by
        rw [← e₂.target]
        rw [mapV_term ]
        congr
        apply p.mapE_localSection
      let ⟨w₁, tail, pf₁, pf₂⟩ := lift b₂  p v₁' term_vert 
      let edge₁ : EdgeBetween G₁ v₁ v₁' :=
        ⟨e₁, init_vert, rfl⟩
      exact ⟨w₁, cons edge₁ tail, pf₁, by 
        simp [cons_toList, pf₂]
        apply p.mapE_localSection⟩


def Morphism.pathMapAux {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (f: Morphism G₁ G₂) (v₁ w₁: V₁) (p: G₁.EdgePath v₁ w₁)
    (v₂ w₂ : V₂)(hv : f.mapV v₁ = v₂)(hw : f.mapV w₁ = w₂) : 
      {path : G₂.EdgePath v₂ w₂ // path.toList = p.toList.map f.mapE} := by 
      match p with
      | nil _ =>
        rw [←hw, hv]
        exact ⟨nil _, by simp [nil_toList]⟩
      | cons e p' => 
        rename_i  w₁'' u'
        let e₁ := f.mapE e.edge
        let init_vert : G₂.ι e₁ = v₂ := by
          rw [←hv, ←e.source, ←mapV_init] 
        let term_vert : G₂.τ e₁ = f.mapV u' := by
          rw [← mapV_term, e.target]
        let edge₂ : EdgeBetween G₂ v₂ (f.mapV u') :=
          ⟨e₁, init_vert, term_vert⟩
        let ⟨tail, ih⟩ := pathMapAux f u' w₁ p' (f.mapV u') w₂ rfl hw
        exact ⟨cons edge₂ tail, by simp [cons_toList, ih]⟩ 

def EdgePath.map {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}{v₁ w₁: V₁} 
    (p: G₁.EdgePath v₁ w₁)(f: Morphism G₁ G₂)  :=
    (f.pathMapAux v₁ w₁ p (f.mapV v₁) (f.mapV w₁) rfl rfl).val

theorem EdgePath.map_toList {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (f: Morphism G₁ G₂) {v₁ w₁: V₁} (p: G₁.EdgePath v₁ w₁) :
      (p.map f).toList = p.toList.map f.mapE := 
      (f.pathMapAux v₁ w₁ p (f.mapV v₁) (f.mapV w₁) rfl rfl).property

def EdgeBetween.map {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (f: Morphism G₁ G₂) {v₁ w₁: V₁} (e: G₁.EdgeBetween v₁ w₁) : 
      G₂.EdgeBetween (f.mapV v₁) (f.mapV w₁) :=
      ⟨f.mapE e.edge, by 
        simp [← f.mapV_init]
        congr
        exact e.source
        , by 
        rw [← mapV_term]
        congr
        exact e.target⟩

theorem EdgeBetween.map_toList {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (f: Morphism G₁ G₂) {v₁ w₁: V₁} (e: G₁.EdgeBetween v₁ w₁) : 
      (e.map f).edge = f.mapE e.edge := by
        simp [EdgeBetween.map, toList]

theorem EdgeBetween.map_bar {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (f: Morphism G₁ G₂) {v₁ w₁: V₁} (e: G₁.EdgeBetween v₁ w₁) : 
      (e.map f).bar = e.bar.map f := by
        ext
        simp [f.mapE_bar, EdgeBetween.map]

namespace Morphism

variable {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂} (f: Morphism G₁ G₂)

theorem append_map {u v w : V₁}(η : EdgePath G₁ u v)(η' : EdgePath G₁ v w):
   (η ++ η').map f = (η.map f) ++ (η'.map f) := by
      apply eq_of_toList_eq
      simp [map_toList, append_toList]
      
theorem cons_map {u v w : V₁}(e : G₁.EdgeBetween u v)(η : EdgePath G₁ v w):
  (cons e η).map f = cons (e.map f) (η.map f) := by
      apply eq_of_toList_eq
      simp [map_toList, EdgeBetween.map_toList, cons_toList]

theorem reverse_map {u v : V₁}(η : EdgePath G₁ u v):
  η.reverse.map f = (η.map f).reverse := by
      apply eq_of_toList_eq
      simp [map_toList, reverse_toList, List.map_reverse]
      congr
      funext e
      simp only [Function.comp, f.mapE_bar]

theorem map_of_reduction {v w : V₁} (η₁ η₂ : EdgePath G₁ v w):
  Reduction η₁ η₂ → Reduction (η₁.map f) (η₂.map f) 
  | Reduction.step u u' e p₁ p₂ => by 
    simp [append_map, cons_map]
    rw [← EdgeBetween.map_bar]
    apply Reduction.step


end Morphism

namespace PathClass

variable {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂} (f: Morphism G₁ G₂)

def map  {v w : V₁}:
  PathClass G₁ v w → PathClass G₂ (f.mapV v) (f.mapV w) := by
    apply Quot.lift (fun η => [[η.map f ]]) 
    intro η₁ η₂ step
    apply Quot.sound
    apply Morphism.map_of_reduction f η₁ η₂ step

theorem map_on_quotient  {v w : V₁}
  (η : EdgePath G₁ v w) : [[ η ]].map f = [[ η.map f ]] := by
    rfl


end PathClass


def asPathLift {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p: Morphism G₁ G₂)[CoveringMap p] {v₁ w₁: V₁} (e: G₁.EdgePath v₁ w₁) :
    PathLift p v₁ rfl   
      (e.map p) := 
    ⟨w₁, e, rfl, by simp [map_toList]⟩

theorem lifts_homotopic {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂} 
    {v₁ w₁ v₂ w₂ : V₁}
    (p : Morphism G₁ G₂)[CoveringMap p]  
    (e₁ : EdgePath G₁ v₁ w₁) (e₂ : EdgePath G₁ v₂ w₂) (hv: v₁ = v₂) :
    e₁.toList.map p.mapE = e₂.toList.map p.mapE →
    e₁.toList = e₂.toList := by
    intro hyp
    match e₁ with
    | nil v => 
      simp [nil_toList] at hyp
      simp [nil_toList]
      symm at hyp
      rw [List.map_eq_nil] at hyp
      symm
      exact hyp
    | cons edg₁ p₁' => 
      match e₂, hv with
      | nil v, _ => 
        simp [nil_toList] at hyp
      | cons edg₂ p₂', rfl => 
        simp [cons_toList] at *
        let ⟨h₁, h₂⟩ := hyp
        have edg_eq : edg₁.edge = edg₂.edge := by 
          let eq₁ := p.localSection_mapE v₁ edg₁.edge (Eq.symm edg₁.source)
          let eq₂ := p.localSection_mapE v₁ edg₂.edge (Eq.symm edg₂.source)
          rw [← eq₁, ← eq₂]
          congr
        simp [edg_eq] 
        apply lifts_homotopic p p₁' p₂' 
        · rw [← edg₁.target, ← edg₂.target, edg_eq]
        · exact h₂

theorem unique_Pathlift {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] {v₁: V₁} {v₂ w₂ : V₂}
    {h₁ h₂ : p.mapV v₁ = v₂}{e: EdgePath G₂ v₂ w₂} :
    (p₁ : PathLift p v₁ h₁ e) → (p₂ : PathLift p v₁ h₂ e) → p₁ = p₂ := by
    intro p₁ p₂
    have eq_edgepath_aux : 
      p₁.path.toList.map p.mapE = 
        p₂.path.toList.map p.mapE := by
      rw [p₁.list_commutes, p₂.list_commutes]
    have eq_edgepath : p₁.path.toList = p₂.path.toList := by
      apply lifts_homotopic p p₁.path p₂.path rfl
      apply eq_edgepath_aux
    have term_eq : p₁.τ = p₂.τ := 
      terminal_eq_of_toList_eq p₁.path p₂.path eq_edgepath rfl
    match p₁, p₂ with
    | ⟨τ₁, path₁, h₁, lc₁⟩, ⟨τ₂, path₂, h₂, lc₂⟩ => 
    have teq : τ₁ = τ₂ := term_eq
    cases teq
    have peq : path₁ = path₂ := by 
      apply eq_of_toList_eq
      assumption
    cases peq
    rfl
          

def PathLift.append {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    {p : Morphism G₁ G₂}[CoveringMap p] {v₁: V₁} {v₂ w₂ u₂ : V₂}
    {h : p.mapV v₁ = v₂}{e: EdgePath G₂ v₂ w₂}{e': EdgePath G₂ w₂ u₂}
    (lift : PathLift p v₁ h e) 
    (lift' : PathLift p lift.τ  lift.lift_terminal e') : 
      PathLift p v₁  h (e ++ e') := 
      {τ := lift'.τ, 
        path := lift.path ++ lift'.path, 
        lift_terminal := lift'.lift_terminal, 
        list_commutes := by 
          simp [append_toList]
          rw [lift.list_commutes, lift'.list_commutes]}
          
theorem EdgePath.lift_append {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] {v₁: V₁} {v₂ w₂ u₂ : V₂}
    {h : p.mapV v₁ = v₂}{e: EdgePath G₂ v₂ w₂}{e': EdgePath G₂ w₂ u₂}: 
      (e ++ e').lift p v₁ h  =
        (e.lift p v₁ h).append 
          (e'.lift p (e.lift p v₁ h).τ  
            (e.lift p v₁ h).lift_terminal) := by
        apply unique_Pathlift 

theorem EdgePath.lift_append_tail {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] {v₁: V₁} {v₂ w₂ u₂ : V₂}
    {h : p.mapV v₁ = v₂}{e: EdgePath G₂ v₂ w₂}{e': EdgePath G₂ w₂ u₂}: 
      ((e ++ e').lift p v₁ h).τ  =
        ((e.lift p v₁ h).append 
          (e'.lift p (e.lift p v₁ h).τ  
            (e.lift p v₁ h).lift_terminal)).τ := by
        simp [lift_append]
        

def PathLift.reverse {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] {v₁: V₁} {v₂ w₂ : V₂}
    {h : p.mapV v₁ = v₂}{e: EdgePath G₂ v₂ w₂} 
    (lift : PathLift p v₁ h e) : 
      PathLift p lift.τ  lift.lift_terminal e.reverse := 
      {τ := v₁, 
        path := lift.path.reverse, 
        lift_terminal := h, 
        list_commutes := by 
          simp [reverse_toList]
          rw [← lift.list_commutes]
          simp [List.map_reverse]
          congr
          funext edge
          simp only [Function.comp, mapE_bar]}

theorem EdgePath.lift_reverse {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] {v₁: V₁} {v₂ w₂ : V₂}
    {h : p.mapV v₁ = v₂}{e: EdgePath G₂ v₂ w₂}: 
      (e.reverse).lift p (e.lift p v₁ h).τ  
        (e.lift p v₁ h).lift_terminal  = 
        (e.lift p v₁ h).reverse := by
        apply unique_Pathlift

def PathLift.cons_bar_cons {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    {p : Morphism G₁ G₂}[CoveringMap p] {v₁: V₁} {v₂ w₂ w₂' : V₂}
    {h : p.mapV v₁ = v₂}{e: EdgeBetween G₂ v₂ w₂'}{e': EdgePath G₂ v₂ w₂}(lift' : PathLift p v₁  h e') : 
      PathLift p v₁ h (cons e (cons e.bar e')) := 
      let edgeLift := p.localSection v₁ e.edge (by rw [h, e.source])
      let edgeBetween : EdgeBetween G₁ v₁ (G₁.τ edgeLift) := 
          ⟨edgeLift, p.init_localSection _ _ _, rfl⟩ 
          
      {τ := lift'.τ, 
        path := cons edgeBetween (cons edgeBetween.bar lift'.path), 
        lift_terminal := lift'.lift_terminal, 
        list_commutes := by 
          simp [cons_toList, p.mapE_localSection, EdgeBetween.bar]
          apply And.intro
          · rw [p.mapE_bar, p.mapE_localSection]
          · rw [lift'.list_commutes]}


theorem homotopy_step_lift {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    {p : Morphism G₁ G₂}[CoveringMap p] {v₁: V₁} {v₂ w₂ w₂' u₂  : V₂}
    {h : p.mapV v₁ = v₂}{η₁: EdgePath G₂ v₂ w₂}{e: EdgeBetween G₂ w₂ w₂'}{η₂: EdgePath G₂ w₂ u₂}:
    ((η₁ ++ (cons e (cons e.bar η₂))).lift p v₁  h ).pathClass = 
    ((η₁ ++ η₂).lift p v₁  h).pathClass := by
  let θ₁ := η₁.lift p v₁ h
  let w₁ := θ₁.τ
  let hw : p.mapV w₁ = w₂ := θ₁.lift_terminal
  let edgeLift := p.localSection w₁ e.edge (by rw [hw, e.source])
  let e' : EdgeBetween G₁ w₁ (G₁.τ edgeLift) := 
          ⟨edgeLift, p.init_localSection _ _ _, rfl⟩ 
  let θ₂ := η₂.lift p w₁ hw 
  let liftTailCanc : PathLift p w₁ hw (cons e (cons e.bar η₂)) :=
    {τ := θ₂.τ, 
        path := cons e' (cons e'.bar θ₂.path), 
        lift_terminal := θ₂.lift_terminal, 
        list_commutes := by 
          simp [cons_toList, p.mapE_localSection, EdgeBetween.bar]
          apply And.intro
          · rw [p.mapE_bar, p.mapE_localSection]
          · rw [θ₂.list_commutes]}
  let liftCanc :=
    θ₁.append liftTailCanc
  have splitLift :
    (η₁ ++ (cons e (cons e.bar η₂))).lift p v₁ h  =
      liftCanc := by
        apply unique_Pathlift
  rw [splitLift]
  have splitLift' :
    (η₁ ++ η₂).lift p v₁ h =
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
    (h : p.mapV v₁ = v₂): PathClass G₂ v₂ w₂ → 
    PathClassFrom G₁ v₁ := by
  apply Quot.lift (fun (η₂: EdgePath G₂ v₂ w₂) => (η₂.lift p v₁ h).pathClass)
  intro η₂ η₂' red
  induction red
  apply homotopy_step_lift

theorem homotopyLift_of_path {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    {p : Morphism G₁ G₂}[CoveringMap p] {v₁: V₁} {v₂ w₂   : V₂}
    {h : p.mapV v₁ = v₂} (e : EdgePath G₂ v₂ w₂) :
    homotopyLift p v₁ h [[ e ]] = 
      (e.lift p v₁ h).pathClass := by
    rfl

def liftClass {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) (v₂ w₂ : V₂)
    (h : p.mapV v₁ = v₂)(e: EdgePath G₂ v₂ w₂): 
    PathClassFrom G₁ v₁ :=
  (e.lift p v₁ h).pathClass

theorem liftClass_eq_of_homotopic {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) {v₂ w₂   : V₂}
    (h : p.mapV v₁ = v₂) {e₁ e₂ : EdgePath G₂ v₂ w₂} 
    (red : [[ e₁ ]] = [[ e₂ ]]) :
    liftClass p v₁ v₂ w₂ h e₁ = liftClass p v₁ v₂ w₂ h  e₂ := by
    simp [liftClass, ← homotopyLift_of_path]
    congr

def liftTerminal {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) {v₂ w₂ : V₂}
    (h : p.mapV v₁ = v₂)(e: EdgePath G₂ v₂ w₂) : V₁:=
  (liftClass p v₁ v₂ w₂ h e).τ

theorem liftTerminal_eq_of_homotopic {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p : Morphism G₁ G₂)[CoveringMap p] (v₁: V₁) {v₂ w₂   : V₂}
    (h : p.mapV v₁ = v₂) {e₁ e₂ : EdgePath G₂ v₂ w₂} 
    (red : [[ e₁ ]] = [[ e₂ ]]) :
    liftTerminal p v₁ h e₁ = liftTerminal p v₁ h  e₂ := by
    simp [liftTerminal]
    rw [liftClass_eq_of_homotopic _ _ _ red]

theorem lift_of_proj {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p: Morphism G₁ G₂)[CoveringMap p] {v₁ w₁: V₁} (e: G₁.EdgePath v₁ w₁):
    (e.map p).lift p v₁ rfl   = ⟨w₁, e, rfl, by simp [map_toList]⟩ := by
    apply unique_Pathlift

theorem proj_injective {G₁ : Graph V₁ E₁} {G₂ : Graph V₂ E₂}
    (p: Morphism G₁ G₂)[CoveringMap p] {v₁ w₁: V₁} 
    (e₁ e₂: G₁.EdgePath v₁ w₁): [[ e₁.map p ]] = [[ e₂.map p ]] → [[ e₁ ]] = [[ e₂ ]] := by
    intro hyp
    let lem := 
      liftClass_eq_of_homotopic p v₁ rfl hyp
    simp [liftClass, PathLift.pathClass] at lem
    rw [lift_of_proj] at lem
    rw [lift_of_proj] at lem
    simp at lem
    exact lem

end Graph