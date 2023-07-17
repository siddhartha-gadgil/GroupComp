import GroupComp.Graph.Covering
import GroupComp.Graph.ReducedPaths
import Mathlib
namespace Graph

open EdgePath PathClass

variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]


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
deriving DecidableEq

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

open Edge

def basepoint : Vert G x₀  := 
  ⟨x₀, EdgePath.nil _, reduced_nil⟩

def rayToRev (G: Graph V E)(x₀ τ : V)(p : EdgePath G τ x₀)
  (hyp : reduced p.reverse)  : 
  EdgePath  (Guniv G x₀) (basepoint G x₀) ⟨τ, p.reverse, hyp⟩   := by
  match p, hyp with
  | nil _,  hyp => apply nil 
  | cons e p', hyp' => 
    rename_i x₀' u
    have red_cons : reduced (cons e p') := by
      rw [← reverse_reverse (cons e p')]
      apply reverse_reduced
      assumption
    have red_p' : reduced p' := by
      apply tail_reduced e p' red_cons
    have red' : reduced p'.reverse := by
      apply reverse_reduced
      assumption
    have init := rayToRev G x₀ u p' red'
    apply init.concat
    let edge : Edge G x₀ := ⟨u, τ, e.bar, p'.reverse, red'⟩ 
    let iv : Vert G x₀ := ⟨u, reverse p', red'⟩
    let τv : Vert G x₀ := ⟨τ, (cons e p').reverse, hyp'⟩
    show EdgeBetween (Guniv G x₀) iv τv
    exact ⟨edge, rfl, (by 
      show edge.terminal = ⟨τ, (cons e p').reverse, hyp'⟩
      simp [terminal, reducedConcat]
      congr
      apply redCons_eq_cons_of_reduced
      assumption)⟩  
    
theorem rayToRev_proj_list (G: Graph V E)(x₀ τ : V)(p : EdgePath G τ x₀)
  (hyp : reduced p.reverse) :
  (rayToRev G x₀ τ p hyp).toEdgeList.map (fun e ↦ e.nxt.edge) = 
    p.toEdgeList.reverse.map (G.bar) := by
    induction p with
  | nil _ => 
    simp [rayToRev, nil_edgeList]    
  | cons e p' ih => 
    rename_i x₀' u u'
    have red_cons : reduced (cons e p') := by
      rw [← reverse_reverse (cons e p')]
      apply reverse_reduced
      assumption
    have red_p' : reduced p' := by
      apply tail_reduced e p' 
      assumption
    have red' : reduced p'.reverse := by
      apply reverse_reduced
      assumption
    simp [rayToRev, cons_edgeList, edgeList_concat, ih red']    

def shiftTarget {G: Graph V E}{v w w' : V}
  (p : EdgePath G v w)(eql : w = w'):  EdgePath G v w' := by
  match p, w', eql with
  | nil _, _, rfl => 
    exact (nil v)
  | cons e p', w', eql => 
    exact cons e (shiftTarget p' eql)

theorem edgeList_shiftTarget {G: Graph V E}{v w w' : V}
  (p : EdgePath G v w)(eql : w = w'):
  (shiftTarget p eql).toEdgeList = p.toEdgeList := by
  match p, w', eql with
  | nil _, _, rfl =>
    rename_i v'
    simp [shiftTarget]
  | cons e p', w', eql =>
    simp [shiftTarget, cons_edgeList, edgeList_shiftTarget]
    

def rayTo (G: Graph V E)(x₀ τ : V)(p : EdgePath G x₀ τ)
  (hyp : reduced p)  : 
  EdgePath  (Guniv G x₀) (basepoint G x₀) ⟨τ, p, hyp⟩ := by
    let ray := rayToRev G x₀ τ p.reverse 
      (by simp [reverse_reverse, hyp])
    apply shiftTarget ray
    simp [reverse_reverse]


theorem rayTo_proj_list (G: Graph V E)(x₀ τ : V)(p : EdgePath G x₀ τ)
  (hyp : reduced p) :
  (rayTo G x₀ τ p hyp).toEdgeList.map (fun e ↦ e.nxt.edge) = 
    p.toEdgeList := by    
    simp [rayTo, edgeList_shiftTarget, rayToRev_proj_list, 
      edgeList_reverse, List.map_reverse]
    have : G.bar ∘ G.bar = id := by
      funext x
      show G.bar (G.bar x) = x
      apply G.bar_involution
    simp [this]

def rayLift (G: Graph V E)(x₀ τ : V)(p : EdgePath G x₀ τ)
  (hyp : reduced p) : PathLift (proj G x₀) (basepoint G x₀)
   rfl p := {
    τ := ⟨τ, p, hyp⟩
    path := rayTo G x₀ τ p hyp
    lift_term := rfl
    list_commutes := by
      simp [proj]
      simp [rayTo_proj_list]
  }  

theorem pathLift_of_reduced {G: Graph V E}{x₀ τ: V}(p : EdgePath G x₀ τ)
  (hyp : reduced p) : 
    pathLift (proj G x₀) (basepoint G x₀) rfl p = 
      rayLift G x₀ τ p hyp := by
      apply unique_Pathlift

theorem reduced_liftTerm {G: Graph V E}{x₀ τ: V}(p : EdgePath G x₀ τ)
  (hyp : reduced p) :
    liftTerm (proj G x₀) (basepoint G x₀) x₀ τ rfl p = 
      ⟨τ, p, hyp⟩ := by
      simp [liftTerm, liftClass, pathLift_of_reduced p hyp, rayLift]
      rfl

theorem reduced_unique {G: Graph V E}(x₀ τ: V){p₁ p₂ : EdgePath G x₀ τ}
  (hyp₁ : reduced p₁)(hyp₂ : reduced p₂):
    [[ p₁ ]] = [[ p₂ ]] → p₁ = p₂ := by
      intro hyp
      have leq :
        liftTerm (proj G x₀) (basepoint G x₀) x₀ τ rfl p₁ =
        liftTerm (proj G x₀) (basepoint G x₀) x₀ τ rfl p₂ := by
        simp [liftTerm]
        apply congrArg 
        apply liftClass_eq_of_equiv
        assumption
      simp [reduced_liftTerm p₁ hyp₁, reduced_liftTerm p₂ hyp₂] at leq
      exact leq

theorem homotopic_iff_reduction_eq {G: Graph V E}(x₀ τ: V)
  (p₁ p₂ : EdgePath G x₀ τ):
    [[ p₁ ]] = [[ p₂ ]] ↔ reduction p₁ = reduction p₂ := by 
    apply Iff.intro
    · intro eql
      rw [← reduction_equiv_self p₁, ← reduction_equiv_self p₂] at eql
      have red₁ : reduced (reduction p₁) := by
        apply reduction_reduced
      have red₂ : reduced (reduction p₂) := by
        apply reduction_reduced
      exact reduced_unique x₀ τ red₁ red₂ eql
    · intro hyp
      rw [← reduction_equiv_self p₁, ← reduction_equiv_self p₂]
      rw [hyp]  

theorem homotopic_of_liftTerm_eq  {G: Graph V E}(x₀ τ: V)
  {p₁ p₂ : EdgePath G x₀ τ} : 
  liftTerm (proj G x₀) (basepoint G x₀) x₀ τ rfl p₁ =
        liftTerm (proj G x₀) (basepoint G x₀) x₀ τ rfl p₂ → 
    [[ p₁ ]] = [[ p₂ ]] := by
    intro hyp
    have red₁ :  [[ reduction p₁ ]] = [[ p₁ ]] := by
      apply reduction_equiv_self
    have red₂ :  [[ reduction p₂ ]] = [[ p₂ ]] := by
      apply reduction_equiv_self
    let l₁ := 
      liftTerm_eq_of_equiv (proj G x₀) (basepoint G x₀) x₀ τ rfl red₁
    let l₂ :=
      liftTerm_eq_of_equiv (proj G x₀) (basepoint G x₀) x₀ τ rfl red₂
    rw [←l₁, ← l₂] at hyp
    rw [reduced_liftTerm (reduction p₁) (reduction_reduced p₁)] at hyp
    rw [reduced_liftTerm (reduction p₂) (reduction_reduced p₂)] at hyp
    simp at hyp
    rw [homotopic_iff_reduction_eq] 
    exact hyp

